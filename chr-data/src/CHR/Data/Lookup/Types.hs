{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

-------------------------------------------------------------------------------------------
-- Abstraction of Map like datatypes providing lookup
-------------------------------------------------------------------------------------------

module CHR.Data.Lookup.Types
  (
    Lookup(..)
  , LookupApply(..)

  , alterDefault
  
  )
  where

-------------------------------------------------------------------------------------------
import qualified Data.Set as Set
import           Control.Arrow
import           Prelude                     hiding (lookup, map)
import qualified Data.List                   as List
-------------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------------
-- Lookup
-------------------------------------------------------------------------------------------

-- | Class interface uses same names as Data.Map.
-- Instances must define: 'lookup', 'findMin', 'findMax', 'fromList', 'toList', 'null', 'alter'.
-- Union is left-biased in that left operand values overwrite right operand values, but all other context/info (if any and/or relevant, like scope) is inherited from the right one.
class Lookup c k v | c -> k, c -> v where
  -- core functionality
  -- extraction
  lookup        :: k -> c -> Maybe v
  {-
  findMin       :: c -> (k, v)
  findMax       :: c -> (k, v)
  -}
  -- (de)construction
  fromList      :: [(k,v)] -> c
  toList        :: c -> [(k,v)]
  -- properties
  null          :: c -> Bool
  size          :: c -> Int
  -- update catchall
  alter         :: (Maybe v -> Maybe v) -> k -> c -> c
 
  -- derived functionality, included as to allow optimization
  singleton     :: k -> v -> c
  empty         :: c
  insertWith    :: (v -> v -> v) -> k -> v -> c -> c
  insert        :: k -> v -> c -> c
  unionWith     :: (v -> v -> v) -> c -> c -> c
  union         :: c -> c -> c
  unionsWith    :: (v -> v -> v) -> [c] -> c
  unions        :: [c] -> c
  delete        :: k -> c -> c
  keys          :: c -> [k]
  keysSet       :: Ord k => c -> Set.Set k
  elems         :: c -> [v]
  map           :: (v -> v) -> c -> c

  -- defs for functions of which def is optional 
  singleton k v         = fromList [(k,v)]
  empty                 = fromList []
  insertWith f k v c    = alter (Just . maybe v (f v)) k c
  insert                = insertWith const
  unionWith f c1 c2     = foldr (uncurry $ insertWith f) c2 $ toList c1
  union                 = unionWith const
  unionsWith f []       = empty
  unionsWith f l        = foldr1 (unionWith f) l
  unions                = unionsWith const
  delete                = alter (const Nothing)
  keys                  = List.map fst . toList
  keysSet               = Set.fromList . keys
  elems                 = List.map snd . toList
  map f                 = fromList . List.map (second f) . toList
  null c                = size c == 0

-- | Default for 'alter' when 'lookup', 'insert' (or 'inserWith'), and 'delete' are defined
alterDefault :: Lookup c k v => (Maybe v -> Maybe v) -> k -> c -> c
alterDefault f k c = case f $ lookup k c of
    Just v -> insert k v c
    _      -> delete k c

-------------------------------------------------------------------------------------------
-- Lookup application, fixing the combination
-------------------------------------------------------------------------------------------

class LookupApply l1 l2 where
  apply :: l1 -> l2 -> l2
