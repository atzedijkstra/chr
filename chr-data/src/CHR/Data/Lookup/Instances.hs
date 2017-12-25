{-# LANGUAGE UndecidableInstances #-}

-------------------------------------------------------------------------------------------
-- Abstraction of Map like datatypes providing lookup
-------------------------------------------------------------------------------------------

module CHR.Data.Lookup.Instances
  (
  
  )
  where

-------------------------------------------------------------------------------------------
import qualified Data.IntMap                as IMap
import qualified Data.Map                   as Map
import qualified Data.HashMap.Strict        as MapH
import qualified Data.Set                   as Set
import qualified CHR.Data.VecAlloc          as VAr
import           Data.Hashable
import           Data.Array.IArray          as IAr
import           CHR.Data.Lookup.Types
-------------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------------
-- Instances: Lookup
-------------------------------------------------------------------------------------------

instance Ord k => Lookup (Map.Map k v) k v where
  lookup            = Map.lookup
  {-
  findMin           = Map.findMin
  findMax           = Map.findMax
  -}
  fromList          = Map.fromList
  toList            = Map.toList
  null              = Map.null
  size              = Map.size
  alter             = Map.alter
  
  -- optional
  unionWith         = Map.unionWith
  insertWith        = Map.insertWith
  delete            = Map.delete
  singleton         = Map.singleton
  empty             = Map.empty
  keys              = Map.keys
  keysSet           = Map.keysSet
  elems             = Map.elems
  map               = Map.map

instance (Eq k, Hashable k) => Lookup (MapH.HashMap k v) k v where
  lookup            = MapH.lookup
  {-
  findMin           = Map.findMin
  findMax           = Map.findMax
  -}
  fromList          = MapH.fromList
  toList            = MapH.toList
  null              = MapH.null
  size              = MapH.size
  alter             = MapH.alter
  
  -- optional
  unionWith         = MapH.unionWith
  insertWith        = MapH.insertWith
  delete            = MapH.delete
  singleton         = MapH.singleton
  empty             = MapH.empty
  keys              = MapH.keys
  -- keysSet           = MapH.keysSet
  elems             = MapH.elems
  map               = MapH.map

instance Lookup (IMap.IntMap v) IMap.Key v where
  lookup            = IMap.lookup
  {-
  findMin           = IMap.findMin
  findMax           = IMap.findMax
  -}
  fromList          = IMap.fromList
  toList            = IMap.toList
  null              = IMap.null
  size              = IMap.size
  alter             = IMap.alter

  -- optional
  unionWith         = IMap.unionWith
  insertWith        = IMap.insertWith
  delete            = IMap.delete
  singleton         = IMap.singleton
  empty             = IMap.empty
  keys              = IMap.keys
  elems             = IMap.elems
  map               = IMap.map
  -- keysSet            = IMap.keysSet

{-
-- | A rather costly inefficient implementation...
instance (Ix i, IArray a e) => Lookup (a i e) i e where
  lookup i a        = if inRange (bounds a) i then Just (a ! i) else Nothing
  {-
  findMin a         = (l, a ! l)
                    where (l,_) = bounds a
  findMax a         = (u, a ! u)
                    where (_,u) = bounds a
  -}
  insertWith f k v c= unionWith f (singleton k v) c
  unionWith f a1 a2 = accum f (array (min l1 l2, max u1 u2) (toList a1)) (toList a2)
                    where (l1,u1) = bounds a1
                          (l2,u2) = bounds a2
  fromList l        = array (minimum ixs, maximum ixs) l
                    where ixs = map fst l
  toList            = assocs
  null  a           = h < l
                    where (l,h) = bounds a
  alter             = alterDefault
  delete            = error "instance Lookup for IArray: no impl for delete"
-}

instance Lookup (VAr.VecAlloc e) Int e where
  lookup            = VAr.lookup
  alter             = VAr.alter
  toList            = VAr.toList
  fromList          = VAr.fromList
  null              = VAr.null

-------------------------------------------------------------------------------------------
-- Instances: LookupApply
-------------------------------------------------------------------------------------------

{-
instance {-# OVERLAPPABLE #-} Lookup l k v => LookupApply l l where
  apply = union
-}
  
