{-# LANGUAGE CPP, StandaloneDeriving #-}

-------------------------------------------------------------------------------------------
--- Run length encoded list, to be used as an identification of scope in UHC
-------------------------------------------------------------------------------------------

module UHC.Util.RLList
  ( -- * Run length list
    RLList(..)
  , concat, singleton, empty, toList, fromList
  
    -- * Predicates, observations
  , length, null
  , isPrefixOf
  
    -- * Misc
  , inits, init, initLast
  , headTail
  )
  where

import           Prelude hiding (length, init, null, concat)
import qualified Prelude as P
import           Data.Maybe
import qualified Data.List as L
import           Data.List hiding (concat, init, null, isPrefixOf, length, inits, singleton)
import           Control.Monad
import           UHC.Util.Utils
import           UHC.Util.Binary
import           UHC.Util.Serialize

-------------------------------------------------------------------------------------------
--- Run length encoded list
-------------------------------------------------------------------------------------------

newtype RLList a
  = RLList { unRLList :: [(a,Int)] }
  deriving (Eq)

instance Ord a => Ord (RLList a) where
  (RLList [])           `compare` (RLList [])           = EQ
  (RLList [])           `compare` (RLList _ )           = LT
  (RLList _ )           `compare` (RLList [])           = GT
  (RLList ((x1,c1):l1)) `compare` (RLList ((x2,c2):l2)) | x1 == x2 = if c1 == c2
                                                                     then RLList l1 `compare` RLList l2
                                                                     else c1 `compare` c2
                                                        | x1 <  x2 = LT
                                                        | x1 >  x2 = GT

instance Show a => Show (RLList a) where
  show = show . toList

concat :: Eq a => RLList a -> RLList a -> RLList a
concat (RLList []) rll2  = rll2
concat rll1 (RLList [])  = rll1
concat (RLList l1) (RLList l2@(h2@(x2,c2):t2))
                            | x1 == x2  = RLList (h1 ++ [(x1,c1+c2)] ++ t2)
                            | otherwise = RLList (l1 ++ l2)
                            where (h1,t1@(x1,c1)) = fromJust (initlast l1)

empty :: RLList a
empty = RLList []

singleton :: a -> RLList a
singleton x = RLList [(x,1)]

toList :: RLList a -> [a]
toList (RLList l) = concatMap (\(x,c) -> replicate c x) l

fromList :: Eq a => [a] -> RLList a
fromList l = RLList [ (x,L.length g) | g@(x:_) <- group l ]

length :: RLList a -> Int
length (RLList l) = sum $ map snd l

null :: RLList a -> Bool
null (RLList []) = True
null (RLList _ ) = False

isPrefixOf :: Eq a => RLList a -> RLList a -> Bool
isPrefixOf (RLList []) _ = True
isPrefixOf _ (RLList []) = False
isPrefixOf (RLList ((x1,c1):l1)) (RLList ((x2,c2):l2))
                            | x1 == x2  = if c1 < c2
                                          then True
                                          else if c1 > c2
                                          then False
                                          else isPrefixOf (RLList l1) (RLList l2)
                            | otherwise = False

-------------------------------------------------------------------------------------------
--- Misc
-------------------------------------------------------------------------------------------

initLast :: Eq a => RLList a -> Maybe (RLList a,a)
initLast (RLList l ) = il [] l
                        where il acc [(x,1)]    = Just (RLList (reverse acc),x)
                              il acc [(x,c)]    = Just (RLList (reverse ((x,c-1):acc)),x)
                              il acc (a:as)     = il (a:acc) as
                              il _   _          = Nothing

init :: Eq a => RLList a -> RLList a
init = fst . fromJust . initLast

inits :: Eq a => RLList a -> [RLList a]
inits = map fromList . L.inits . toList

headTail :: RLList a -> Maybe (a,RLList a)
headTail (RLList [])        = Nothing
headTail (RLList ((x,1):t)) = Just (x,RLList t)
headTail (RLList ((x,c):t)) = Just (x,RLList ((x,c-1):t))

-------------------------------------------------------------------------------------------
--- Instances: Typeable, Data
-------------------------------------------------------------------------------------------

#if __GLASGOW_HASKELL__ >= 708
deriving instance Typeable  RLList
#else
deriving instance Typeable1 RLList
#endif
-- deriving instance Data x => Data (RLList x)

-------------------------------------------------------------------------------------------
--- Instances: Binary, Serialize
-------------------------------------------------------------------------------------------

instance Binary a => Binary (RLList a) where
  put (RLList a) = put a
  get = liftM RLList get
