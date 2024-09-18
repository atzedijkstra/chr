{-| Relation via pair of maps for domain and range, for faster lookup in 2 directions.
    Incomplete w.r.t. corresponding UHC.Util.Rel
-}
module UHC.Util.RelMap
  ( Rel
  , empty
  , toDomList, toRngList
  , toList, fromList
  , singleton
  , dom, rng
  , restrictDom, restrictRng
  , mapDom, mapRng
  -- , partitionDom, partitionRng
  -- , intersection, difference
  , union, unions
  , insert
  , deleteDom, delete
  , deleteRng
  
  , applyDomMbSet, applyRngMbSet
  , applyDomSet, applyRngSet
  , applyDom, applyRng
  , apply, applyInverse
  
  , lookupDom, lookupRng
  , lookup, lookupInverse
  
  , toDomMap, toRngMap
  -- , mapDomRng
  )
  where

import           Prelude hiding (lookup)
import           Control.Monad
import qualified Data.Map as Map
import qualified Data.Set as Set
import           UHC.Util.AssocL
import           UHC.Util.Binary
import           UHC.Util.Serialize

-------------------------------------------------------------------------
-- Relation map
-------------------------------------------------------------------------

-- | Map used in a relation
type RelMap a b = Map.Map a (Set.Set b)

-- | Delete key in range of RelMap
relmapDeleteRng :: Ord b => b -> RelMap a b -> RelMap a b
relmapDeleteRng x r = snd $ Map.mapEither (eith x) r
  where eith x ds = if Set.null ds' then Left ds else Right ds'
          where (ds1,ds2) = Set.split x ds
                ds' = Set.union ds1 ds2

-------------------------------------------------------------------------
-- Relation
-------------------------------------------------------------------------

-- | Relation, represented as 2 maps from domain to range and the inverse, thus allowing faster lookup at the expense of some set like operations more expensive.
data Rel a b
  = Rel
     { relDomMp :: RelMap a b       -- ^ from domain to range
     , relRngMp :: RelMap b a       -- ^ from range to domain
     }

-- | As assocation list where each domain value only occurs once and the range as list
toDomList :: Rel a b -> [(a,[b])]
toDomList (Rel m _) = [ (d, Set.toList rs) | (d,rs) <- Map.toList m ]

-- | As assocation list where each range value only occurs once and the domain as list
toRngList :: Rel a b -> [([a],b)]
toRngList (Rel _ m) = [ (Set.toList ds, r) | (r,ds) <- Map.toList m ]

-- | As assocation list
toList :: Rel a b -> [(a,b)]
toList rel = [ (d,r) | (d,rs) <- toDomList rel, r <- rs ]

-- | From association list
fromList :: (Ord a, Ord b) => [(a,b)] -> Rel a b
fromList = unions . map (uncurry singleton)

-- | Singleton relation
singleton :: (Ord a, Ord b) => a -> b -> Rel a b
singleton a b = Rel (relMapSingleton a b) (relMapSingleton b a)

-- | Empty relation
empty :: Rel a b
empty = Rel Map.empty Map.empty

-- | Domain of relation
dom :: (Ord a, Ord b) => Rel a b -> Set.Set a
dom = Map.keysSet . relDomMp

-- | Range of relation
rng :: (Ord a, Ord b) => Rel a b -> Set.Set b
rng = Map.keysSet . relRngMp

-- | Filter on domain
restrictDom :: (Ord a, Ord b) => (a -> Bool) -> Rel a b -> Rel a b
restrictDom p (Rel d r) = Rel d' r'
  where d' = Map.filterWithKey (\d r -> p d) d
        r' = relMapInverse d'

-- | Filter on range
restrictRng :: (Ord a, Ord b) => (b -> Bool) -> Rel a b -> Rel a b
restrictRng p (Rel d r) = Rel d' r'
  where r' = Map.filterWithKey (\r d -> p r) r
        d' = relMapInverse r'

-- | Map domain
mapDom :: (Ord b, Ord x) => (a -> x) -> Rel a b -> Rel x b
mapDom f = fromList . assocLMapKey f . toList

-- | Map range
mapRng :: (Ord a, Ord x) => (b -> x) -> Rel a b -> Rel a x
mapRng f = fromList . assocLMapElt f . toList

{-
-- | Partition domain
partitionDom :: (Ord a, Ord b) => (a -> Bool) -> Rel a b -> (Rel a b,Rel a b)
partitionDom f = Set.partition (f . fst)

-- | Partition range
partitionRng :: (Ord a, Ord b) => (b -> Bool) -> Rel a b -> (Rel a b,Rel a b)
partitionRng f = Set.partition (f . snd)

-- | Intersect jointly on domain and range
intersection :: (Ord a, Ord b) => Rel a b -> Rel a b -> Rel a b
intersection = Set.intersection

-- | Difference jointly on domain and range
difference :: (Ord a, Ord b) => Rel a b -> Rel a b -> Rel a b
difference = Set.difference
-}

-- | Union
union :: (Ord a, Ord b) => Rel a b -> Rel a b -> Rel a b
union (Rel d1 r1) (Rel d2 r2) = Rel (Map.unionWith Set.union d1 d2) (Map.unionWith Set.union r1 r2)

-- | Union of list of relations
unions :: (Ord a, Ord b) => [Rel a b] -> Rel a b
unions [ ] = empty
unions [r] = r
unions rs  = foldr union empty rs

-- | Insert
insert :: (Ord a, Ord b) => a -> b -> Rel a b -> Rel a b
insert x y r = singleton x y `union` r

-- | Delete at domain
deleteDom, delete :: (Ord a, Ord b) => a -> Rel a b -> Rel a b
deleteDom x (Rel d r) = Rel (Map.delete x d) (relmapDeleteRng x r)
delete = deleteDom
{-# INLINE delete #-}

-- | Delete at range
deleteRng :: (Ord a, Ord b) => b -> Rel a b -> Rel a b
deleteRng x (Rel d r) = Rel (relmapDeleteRng x d) (Map.delete x r)

-- | Apply relation as a function, possible yielding a non empty set
applyDomMbSet :: (Ord a) => Rel a b -> a -> Maybe (Set.Set b)
applyDomMbSet r a = Map.lookup a (relDomMp r)
{-# INLINE applyDomMbSet #-}

-- | Apply relation as an inverse function, possible yielding a non empty set
applyRngMbSet :: (Ord b) => Rel a b -> b -> Maybe (Set.Set a)
applyRngMbSet r b = Map.lookup b (relRngMp r)
{-# INLINE applyRngMbSet #-}

-- | Apply relation as a function, yielding a possibly empty set
applyDomSet :: (Ord a) => Rel a b -> a -> Set.Set b
applyDomSet r a = maybe Set.empty id $ applyDomMbSet r a
{-# INLINE applyDomSet #-}

-- | Apply relation as an inverse function, yielding a possibly empty set
applyRngSet :: (Ord b) => Rel a b -> b -> Set.Set a
applyRngSet r b = maybe Set.empty id $ applyRngMbSet r b
{-# INLINE applyRngSet #-}

-- | Apply relation as a function, aka lookup, picking an arbitrary value in case of multiples
applyDom :: (Ord a) => Rel a b -> a -> Maybe b
applyDom r a = fmap Set.findMin $ applyDomMbSet r a
{-# INLINE applyDom #-}

-- | Apply relation as an inverse function, aka lookup, picking an arbitrary value in case of multiples
applyRng :: (Ord b) => Rel a b -> b -> Maybe a
applyRng r b = fmap Set.findMin $ applyRngMbSet r b
{-# INLINE applyRng #-}

-- | Apply relation as a function
apply :: (Ord a) => Rel a b -> a -> [b]
apply r a = maybe [] Set.toList $ applyDomMbSet r a
{-# INLINE apply #-}

-- | Apply relation as an inverse function
applyInverse :: (Ord b) => Rel a b -> b -> [a]
applyInverse r b = maybe [] Set.toList $ applyRngMbSet r b
{-# INLINE applyInverse #-}

-- | Alias for apply in more conventional terms
lookupDom, lookup :: (Ord a) => a -> Rel a b -> Maybe b
lookupDom = flip applyDom
{-# INLINE lookupDom #-}
lookup    = lookupDom
{-# INLINE lookup #-}

-- | Alias for apply in more conventional terms
lookupRng, lookupInverse :: (Ord b) => b -> Rel a b -> Maybe a
lookupRng     = flip applyRng
{-# INLINE lookupRng #-}
lookupInverse = lookupRng
{-# INLINE lookupInverse #-}

-- | As a Map keyed on domain
toDomMap :: Ord a => Rel a b -> Map.Map a [b]
toDomMap = Map.map Set.toList . relDomMp

-- | As a Map keyed on range
toRngMap :: Ord b => Rel a b -> Map.Map b [a]
toRngMap = Map.map Set.toList . relRngMp

{-
-- | Map over domain and range
mapDomRng :: (Ord a, Ord b, Ord a', Ord b') => ((a,b) -> (a',b')) -> Rel a b -> Rel a' b'
mapDomRng = Set.map
-}

-------------------------------------------------------------------------
-- Util
-------------------------------------------------------------------------

-- | Singleton
relMapSingleton :: (Ord a, Ord b) => a -> b -> RelMap a b
relMapSingleton d r = Map.singleton d (Set.singleton r)

-- | Take the inverse of a map used in relation
relMapInverse :: (Ord a, Ord b) => RelMap a b -> RelMap b a
relMapInverse m = Map.unionsWith Set.union [ relMapSingleton r d | (d,rs) <- Map.toList m, r <- Set.toList rs ]

-------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------

instance (Ord b, Ord a, Binary a, Binary b) => Binary (Rel a b) where
  put = put . toList
  get = liftM fromList get

instance (Ord b, Ord a, Serialize a, Serialize b) => Serialize (Rel a b) where
  sput = sput . toList
  sget = liftM fromList sget
