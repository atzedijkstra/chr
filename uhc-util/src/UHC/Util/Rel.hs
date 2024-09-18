{-| Relation via Set of tuples
-}
module UHC.Util.Rel
  ( Rel
  , empty
  , toList, fromList
  , singleton
  , dom, rng
  , restrictDom, restrictRng
  , mapDom, mapRng
  , partitionDom, partitionRng
  , intersection, difference, union, unions
  , apply
  , toDomMap, toRngMap
  , mapDomRng
  )
  where

import qualified Data.Map as Map
import qualified Data.Set as Set

-------------------------------------------------------------------------
-- Relation
-------------------------------------------------------------------------

type Rel a b = Set.Set (a,b)

-- | As assocation list
toList :: Rel a b -> [(a,b)]
toList = Set.toList

-- | From association list
fromList :: (Ord a, Ord b) => [(a,b)] -> Rel a b
fromList = Set.fromList

-- | Singleton relation
singleton :: (Ord a, Ord b) => a -> b -> Rel a b
singleton a b = fromList [(a,b)]

-- | Empty relation
empty :: Rel a b
empty = Set.empty

-- | Domain of relation
dom :: (Ord a, Ord b) => Rel a b -> Set.Set a
dom = Set.map fst

-- | Range of relation
rng :: (Ord a, Ord b) => Rel a b -> Set.Set b
rng = Set.map snd

-- | Filter on domain
restrictDom :: (Ord a, Ord b) => (a -> Bool) -> Rel a b -> Rel a b
restrictDom p = Set.filter (p . fst)

-- | Filter on range
restrictRng :: (Ord a, Ord b) => (b -> Bool) -> Rel a b -> Rel a b
restrictRng p = Set.filter (p . snd)

-- | Map domain
mapDom :: (Ord a, Ord b, Ord x) => (a -> x) -> Rel a b -> Rel x b
mapDom f = Set.map (\(a,b) -> (f a,b))

-- | Map range
mapRng :: (Ord a, Ord b, Ord x) => (b -> x) -> Rel a b -> Rel a x
mapRng f = Set.map (\(a,b) -> (a,f b))

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

-- | Union
union :: (Ord a, Ord b) => Rel a b -> Rel a b -> Rel a b
union = Set.union

-- | Union of list of relations
unions :: (Ord a, Ord b) => [Rel a b] -> Rel a b
unions = Set.unions

-- | Apply relation as a function
apply :: (Ord a, Ord b) => Rel a b -> a -> [b]
apply r a = Set.toList $ rng $ restrictDom (==a) $ r

-- | As a Map keyed on domain
toDomMap :: Ord a => Rel a b -> Map.Map a [b]
toDomMap r = Map.unionsWith (++) [ Map.singleton a [b] | (a,b) <- toList r ]

-- | As a Map keyed on range
toRngMap :: Ord b => Rel a b -> Map.Map b [a]
toRngMap r = Map.unionsWith (++) [ Map.singleton b [a] | (a,b) <- toList r ]

-- | Map over domain and range
mapDomRng :: (Ord a, Ord b, Ord a', Ord b') => ((a,b) -> (a',b')) -> Rel a b -> Rel a' b'
mapDomRng = Set.map

