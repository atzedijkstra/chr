{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

-------------------------------------------------------------------------------------------
-- | Vector intended for densily filled entries close to 0, > 0.
-- In situ updates are not supposed to happen often.
-------------------------------------------------------------------------------------------

module CHR.Data.VecAlloc
  ( VecAlloc
  
  , empty
  , alter
  , lookup
  , toList
  , fromList
  , null
  
  , size
  )
  where

-------------------------------------------------------------------------------------------
import           Prelude                        hiding (lookup, map, null)
import qualified Data.List                      as List
import           Control.Monad
import qualified Data.Vector                    as V
import qualified Data.Vector.Mutable            as MV
import           CHR.Data.Lens
-------------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------------------

data Val v = Init | Noth | Val v

instance Show v => Show (Val v) where
  show (Val v) = show v
  show _       = ""

m2v :: Maybe v -> Val v
m2v = maybe Noth Val
{-# INLINE m2v #-}

v2m :: Val v -> Maybe v
v2m (Val v) = Just v
v2m _       = Nothing
{-# INLINE v2m #-}

-- | VecAlloc e
newtype VecAlloc e
  = VecAlloc
      { _vecallocVec     :: V.Vector (Val e)
      -- , _vecallocFree    :: {-# UNPACK #-} !Int
      }
  deriving Show

mkLabel ''VecAlloc

-------------------------------------------------------------------------------------------
-- VecAlloc e utils
-------------------------------------------------------------------------------------------

-- | Ensure enough free slots
ensure :: Int -> VecAlloc e -> VecAlloc e
ensure sz s@(VecAlloc {_vecallocVec=v})
  | l >= sz   = s
  | otherwise = s {_vecallocVec = v V.++ V.replicate ((sz `max` ((3 * l) `div` 2)) - l) Init}
  where l = V.length v
{-# INLINE ensure #-}

empty :: VecAlloc e
empty = VecAlloc (V.replicate 3 Init) -- 0
{-# INLINE empty #-}

alter :: (Maybe e -> Maybe e) -> Int -> VecAlloc e -> VecAlloc e
alter f k s@(VecAlloc {_vecallocVec=v})
  | k >= V.length v = maybe s (\val -> vecallocVec ^$= V.modify (\v -> MV.write v k (Val val)) $ ensure (k+1) s) $ f Nothing
  | otherwise       = let upd vv = case vv V.! k of
                                     Init  -> V.modify (\v -> MV.write v k (m2v $ f Nothing)) vv
                                     Noth  -> vv V.// [(k, m2v $ f Nothing)]
                                     Val v -> vv V.// [(k, m2v $ f $ Just v)]
                      in  vecallocVec ^$= upd $ s

lookup :: Int -> VecAlloc e -> Maybe e
lookup k (VecAlloc {_vecallocVec=v})
  | k >= V.length v = Nothing
  | otherwise       = v2m $ v V.! k

toList :: VecAlloc e -> [(Int,e)]
toList (VecAlloc {_vecallocVec=v}) = [ (i,v) | (i, Val v) <- zip [0..] $ V.toList v ]

fromList :: [(Int,e)] -> VecAlloc e
fromList [] = empty
fromList l  = vecallocVec ^$= V.modify (\v -> forM_ l $ \(k,x) -> MV.write v k (Val x)) $ ensure (mx+1) empty
  where mx = maximum $ List.map fst l

null :: VecAlloc e -> Bool
null = List.null . toList

{-
unionWith :: (e -> e -> e) -> VecAlloc e -> VecAlloc e -> VecAlloc e
unionWith f (VecAlloc {_vecallocVec=v1}) (VecAlloc {_vecallocVec=v2})
-}

size :: VecAlloc e -> Int
size = V.length . _vecallocVec
