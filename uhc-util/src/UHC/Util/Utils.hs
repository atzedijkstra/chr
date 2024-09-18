{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators, TypeSynonymInstances, FlexibleInstances, DefaultSignatures, UndecidableInstances #-}

module UHC.Util.Utils
  ( module CHR.Utils
  
    -- * Set
  , unionMapSet

    -- * Map
  , inverseMap
  , showStringMapKeys
  
  , mapLookup2', mapLookup2
  
    -- * List
  , hdAndTl', hdAndTl
  -- , maybeNull
  -- , maybeHd
  , wordsBy
  , initlast, initlast2
  , last'
  , firstNotEmpty
  , listSaturate, listSaturateWith
  , spanOnRest
  , filterMb
  -- , splitPlaces
  -- , combineToDistinguishedEltsBy
  , partitionOnSplit
  -- , zipWithN
  
    -- * Tuple
  , tup123to1, tup123to2
  , tup123to12, tup123to23
  , tup12to123
  
  , fst3
  , snd3
  , thd3
  , thd 
  
  , tup1234to1  
  , tup1234to2  
  , tup1234to3  
  , tup1234to4  
  
  , tup1234to12
  , tup1234to13
  , tup1234to14
  , tup1234to23
  , tup1234to24
  , tup1234to34
  
  , tup1234to123
  , tup1234to234
  
  , tup1234to124
  , tup1234to134
  
  , tup123to1234

  , fst4
  , snd4
  , thd4
  , fth4
  , fth 
  
    -- * String
  , strWhite
  , strPad
  , strCapitalize
  , strToLower
  , strToInt
  
  , splitForQualified
  
    -- * Show utils
  , showUnprefixedWithShowTypeable
  , DataAndConName(..)
  , showUnprefixed
  
    -- * Ordering
  -- , orderingLexic
  -- , orderingLexicList
  
    -- * Misc
  -- , panic
  
  -- , isSortedByOn
  -- , sortOnLazy
  -- , sortOn
  -- , sortByOn
  -- , groupOn
  -- , groupByOn
  -- , groupSortOn
  -- , groupSortByOn
  , nubOn
  
  , consecutiveBy
  
  , partitionAndRebuild
  
    -- * Maybe
  -- , panicJust
  , ($?)
  , orMb
  , maybeAnd
  , maybeOr
  
    -- * Graph
  , scc
  
    -- * Monad
  , firstMaybeM
  , breakM
  )
  where

-- import UHC.Util.Pretty
import Data.Char
import Data.List
import Data.Maybe
import Data.Function
import Data.Typeable
import GHC.Generics
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Graph as Graph
import CHR.Utils

-------------------------------------------------------------------------
-- Set
-------------------------------------------------------------------------

-- | Union a set where each element itself is mapped to a set
unionMapSet :: Ord b => (a -> Set.Set b) -> (Set.Set a -> Set.Set b)
unionMapSet f = Set.unions . map f . Set.toList

-------------------------------------------------------------------------
-- Map
-------------------------------------------------------------------------

-- | Inverse of a map
inverseMap :: (Ord k, Ord v') => (k -> v -> (v',k')) -> Map.Map k v -> Map.Map v' k'
inverseMap mk = Map.fromList . map (uncurry mk) . Map.toList

-- | Show keys of map using a separator
showStringMapKeys :: Map.Map String x -> String -> String
showStringMapKeys m sep = concat $ intersperse sep $ Map.keys m

-------------------------------------------------------------------------
-- List
-------------------------------------------------------------------------

-- | Get head and tail, with default if empty list
hdAndTl' :: a -> [a] -> (a,[a])
hdAndTl' _ (a:as) = (a,as)
hdAndTl' n []     = (n,[])

-- | Get head and tail, with panic/error if empty list
hdAndTl :: [a] -> (a,[a])
hdAndTl = hdAndTl' (panic "hdAndTl")
{-# INLINE hdAndTl  #-}

{-
maybeNull :: r -> ([a] -> r) -> [a] -> r
maybeNull n f l = if null l then n else f l
{-# INLINE maybeNull  #-}

maybeHd :: r -> (a -> r) -> [a] -> r
maybeHd n f = maybeNull n (f . head)
{-# INLINE maybeHd  #-}
-}

-- | Split up in words by predicate
wordsBy :: (a -> Bool) -> [a] -> [[a]]
wordsBy p l
  = w l
  where w [] = []
        w l  = let (l',ls') = break p l
               in  l' : case ls' of []       -> []
                                    (_:[])   -> [[]]
                                    (_:ls'') -> w ls''

-- | Possibly last element and init
initlast :: [a] -> Maybe ([a],a)
initlast as
  = il [] as
  where il acc [a]    = Just (reverse acc,a)
        il acc (a:as) = il (a:acc) as
        il _   _      = Nothing

-- | variation on last which returns empty value instead of
last' :: a -> [a] -> a
last' e = maybe e snd . initlast

-- | Possibly last and preceding element and init
initlast2 :: [a] -> Maybe ([a],a,a)
initlast2 as
  = il [] as
  where il acc [a,b]  = Just (reverse acc,a,b)
        il acc (a:as) = il (a:acc) as
        il _   _      = Nothing

-- | First non empty list of list of lists
firstNotEmpty :: [[x]] -> [x]
firstNotEmpty = maybeHd [] id . filter (not . null)

-- | Saturate a list, that is:
-- for all indices i between min and max,
-- if there is no listelement x for which  get x  returns i,
-- add an element  mk i  to the list
listSaturate :: (Enum a,Ord a) => a -> a -> (x -> a) -> (a -> x) -> [x] -> [x]
listSaturate min max get mk xs
  = [ Map.findWithDefault (mk i) i mp | i <- [min..max] ]
  where mp = Map.fromList [ (get x,x) | x <- xs ]

-- | Saturate a list with values from assoc list, that is:
-- for all indices i between min and max,
-- if there is no listelement x for which  get x  returns i,
-- add a candidate from the associationlist (which must be present) to the list
listSaturateWith :: (Enum a,Ord a) => a -> a -> (x -> a) -> [(a,x)] -> [x] -> [x]
listSaturateWith min max get missing l
  = listSaturate min max get mk l
  where mp = Map.fromList missing
        mk a = panicJust "listSaturateWith" $ Map.lookup a mp

-- variant on span, predicate on full list
spanOnRest :: ([a] -> Bool) -> [a] -> ([a],[a])
spanOnRest p []       = ([],[])
spanOnRest p xs@(x:xs')
     | p xs      = (x:ys, zs)
     | otherwise = ([],xs)
                       where (ys,zs) = spanOnRest p xs'

-- | variant on 'filter', where predicate also yields a result
filterMb :: (a -> Maybe b) -> [a] -> [b]
filterMb p = catMaybes . map p
{-# INLINE filterMb #-}

-- | Split at index places (inspired by/from split package). Places should be increasing, starting with an index >= 0.
-- The number of sublists returned is one higher than the number of places.
-- 
-- Examples:
-- >>> splitPlaces [2,3] [1,2,3,4,5,6,7] 
-- [[1,2],[3],[4,5,6,7]]
--
-- >>> splitPlaces [6,7] [1,2,3,4,5,6,7] 
-- [[1,2,3,4,5,6],[7],[]]
--
-- >>> splitPlaces [0,7] [1,2,3,4,5,6,7]
-- [[],[1,2,3,4,5,6,7],[]]
--
-- >>> splitPlaces [0,1,2,3,4,5,6,7] [1,2,3,4,5,6,7] 
-- [[],[1],[2],[3],[4],[5],[6],[7],[]]
splitPlaces
  :: [Int]            -- ^ places
  -> [e]
  -> [[e]]
splitPlaces ps es = spl 0 ps es
  where spl _   []     es = [es]
        spl pos (p:ps) es = es1 : spls
          where (es1,es2) = splitAt (p-pos) es
                spls = spl (pos + length es1) ps es2

{-
-- | Combine [[x1..xn],..,[y1..ym]] to [[x1..y1],[x2..y1],..,[xn..ym]].
--   Each element [xi..yi] is distinct based on the the key k in xi==(k,_)
combineToDistinguishedEltsBy :: (e -> e -> Bool) -> [[e]] -> [[e]]
combineToDistinguishedEltsBy _  []     = []
combineToDistinguishedEltsBy _  [[]]   = []
combineToDistinguishedEltsBy _  [x]    = map (:[]) x
combineToDistinguishedEltsBy eq (l:ls)
  = combine l $ combineToDistinguishedEltsBy eq ls
  where combine l ls
          = concatMap (\e
                         -> mapMaybe (\ll -> maybe (Just (e:ll)) (const Nothing) $ find (eq e) ll)
                                     ls
                      ) l

zipWithN :: ([x] -> y) -> [[x]] -> [y]
zipWithN f l | any null l = []
             | otherwise  = f (map head l) : zipWithN f (map tail l)
-}

-------------------------------------------------------------------------
-- Tupling, untupling
-------------------------------------------------------------------------

tup123to1  (a,_,_) = a
tup123to2  (_,a,_) = a
tup123to3  (_,_,a) = a
{-# INLINE tup123to1  #-}
{-# INLINE tup123to2  #-}
{-# INLINE tup123to3  #-}

tup123to12 (a,b,_) = (a,b)
tup123to23 (_,a,b) = (a,b)
{-# INLINE tup123to12 #-}
{-# INLINE tup123to23 #-}

tup12to123 c (a,b) = (a,b,c)
{-# INLINE tup12to123 #-}

fst3 = tup123to1
snd3 = tup123to2
thd3 = tup123to3
thd  = thd3
{-# INLINE fst3 #-}
{-# INLINE snd3 #-}
{-# INLINE thd3 #-}
{-# INLINE thd  #-}

tup1234to1   (a,_,_,_) = a
tup1234to2   (_,a,_,_) = a
tup1234to3   (_,_,a,_) = a
tup1234to4   (_,_,_,a) = a
{-# INLINE tup1234to1   #-}
{-# INLINE tup1234to2   #-}
{-# INLINE tup1234to3   #-}
{-# INLINE tup1234to4   #-}

tup1234to12  (a,b,_,_) = (a,b)
tup1234to13  (a,_,b,_) = (a,b)
tup1234to14  (a,_,_,b) = (a,b)
tup1234to23  (_,a,b,_) = (a,b)
tup1234to24  (_,a,_,b) = (a,b)
tup1234to34  (_,_,a,b) = (a,b)
{-# INLINE tup1234to12 #-}
{-# INLINE tup1234to13 #-}
{-# INLINE tup1234to14 #-}
{-# INLINE tup1234to23 #-}
{-# INLINE tup1234to24 #-}
{-# INLINE tup1234to34 #-}

tup1234to123 (a,b,c,_) = (a,b,c)
tup1234to234 (_,a,b,c) = (a,b,c)
{-# INLINE tup1234to123 #-}
{-# INLINE tup1234to234 #-}

tup1234to124 (a,b,_,c) = (a,b,c)
tup1234to134 (a,_,b,c) = (a,b,c)
{-# INLINE tup1234to124 #-}
{-# INLINE tup1234to134 #-}

tup123to1234 d (a,b,c) = (a,b,c,d)
{-# INLINE tup123to1234 #-}

fst4 = tup1234to1
snd4 = tup1234to2
thd4 = tup1234to3
fth4 = tup1234to4
fth  = fth4
{-# INLINE fst4 #-}
{-# INLINE snd4 #-}
{-# INLINE thd4 #-}
{-# INLINE fth4 #-}
{-# INLINE fth  #-}

-------------------------------------------------------------------------
-- String
-------------------------------------------------------------------------

-- | Blanks
strWhite :: Int -> String
strWhite sz = replicate sz ' '
{-# INLINE strWhite #-}

-- | Pad upto size with blanks
strPad :: String -> Int -> String
strPad s sz = s ++ strWhite (sz - length s)

-- | Capitalize first letter
strCapitalize :: String -> String
strCapitalize s
  = case s of
      (c:cs) -> toUpper c : cs
      _      -> s

-- | Lower case
strToLower :: String -> String
strToLower = map toLower
{-# INLINE strToLower #-}

-- | Convert string to Int
strToInt :: String -> Int
strToInt = foldl (\i c -> i * 10 + ord c - ord '0') 0

-------------------------------------------------------------------------
-- Split for qualified name
-------------------------------------------------------------------------

-- | Show, additionally removing type name prefix, assuming constructor names are prefixed with type name, possibly with additional underscore (or something like that)
showUnprefixedWithShowTypeable :: (Show x, Typeable x) => Int -> x -> String
showUnprefixedWithShowTypeable extralen x = drop prelen $ show x
  where prelen = (length $ show $ typeOf x) + extralen

-- | Generic constructor name, to be used by show variations
class GDataAndConName f where
  gDataAndConName :: f x -> (String,String)

class DataAndConName x where
  -- | Get datatype and constructor name for a datatype
  dataAndConName :: x -> (String,String)
  
  default dataAndConName :: (Generic x, GDataAndConName (Rep x)) => x -> (String,String)
  dataAndConName = gDataAndConName . from

instance (Datatype d, GDataAndConName x) => GDataAndConName (D1 d x) where
  gDataAndConName d@(M1 x) = let (_,c) = gDataAndConName x in (datatypeName d, c)

instance (GDataAndConName a, GDataAndConName b) => GDataAndConName (a :+: b) where
  gDataAndConName (L1 x) = gDataAndConName x
  gDataAndConName (R1 x) = gDataAndConName x

instance (Constructor c) => GDataAndConName (C1 c x) where
  gDataAndConName c = ("", conName c)

-- | Show, additionally removing type name prefix, assuming constructor names are prefixed with type name, possibly with additional underscore (or something like that)
showUnprefixed :: (DataAndConName x) => Int -> x -> String
showUnprefixed extralen x = drop prelen $ c
  where (d,c) = dataAndConName x
        prelen = (length d) + extralen

-------------------------------------------------------------------------
-- Split for qualified name
-------------------------------------------------------------------------

-- | Split into fragments based on '.' convention for qualified Haskell names
splitForQualified :: String -> [String]
splitForQualified s
    = ws''
    where ws  = wordsBy (=='.') s
          ws' = case initlast2 ws of
                  Just (ns,n,"") -> ns ++ [n ++ "."]
                  _              -> ws
          ws''= case break (=="") ws' of
                  (nq,(_:ns)) -> nq ++ [concatMap ("."++) ns]
                  _ -> ws'

-------------------------------------------------------------------------
-- Misc
-------------------------------------------------------------------------

{-
-- | Error, with message
panic m = error ("panic: " ++ m)
-}

-------------------------------------------------------------------------
-- group/sort/nub combi's
-------------------------------------------------------------------------

{-
isSortedByOn :: (b -> b -> Ordering) -> (a -> b) -> [a] -> Bool
isSortedByOn cmp sel l
  = isSrt l
  where isSrt (x1:tl@(x2:_)) = cmp (sel x1) (sel x2) /= GT && isSrt tl
        isSrt _              = True

-- | A slightly more lazy version of Data.List.sortOn.
-- See also https://github.com/UU-ComputerScience/uhc-util/issues/5 .
sortOnLazy :: Ord b => (a -> b) -> [a] -> [a]
sortOnLazy = sortByOn compare
{-# INLINE sortOnLazy #-}

#if __GLASGOW_HASKELL__ >= 710
#else
-- | The original Data.List.sortOn.
-- See also https://github.com/UU-ComputerScience/uhc-util/issues/5 .
sortOn :: Ord b => (a -> b) -> [a] -> [a]
sortOn = sortOnLazy
{-# INLINE sortOn #-}
#endif

sortByOn :: (b -> b -> Ordering) -> (a -> b) -> [a] -> [a]
sortByOn cmp sel = sortBy (cmp `on` sel) -- (\e1 e2 -> sel e1 `cmp` sel e2)

groupOn :: Eq b => (a -> b) -> [a] -> [[a]]
groupOn sel = groupBy ((==) `on` sel) -- (\e1 e2 -> sel e1 == sel e2)

groupSortOn :: Ord b => (a -> b) -> [a] -> [[a]]
groupSortOn sel = groupOn sel . sortOn sel

groupByOn :: (b -> b -> Bool) -> (a -> b) -> [a] -> [[a]]
groupByOn eq sel = groupBy (eq `on` sel) -- (\e1 e2 -> sel e1 `eq` sel e2)

groupSortByOn :: (b -> b -> Ordering) -> (a -> b) -> [a] -> [[a]]
groupSortByOn cmp sel = groupByOn (\e1 e2 -> cmp e1 e2 == EQ) sel . sortByOn cmp sel
-}

nubOn :: Eq b => (a->b) -> [a] -> [a]
nubOn sel = nubBy ((==) `on` sel) -- (\a1 a2 -> sel a1 == sel a2)

-- | The 'consecutiveBy' function groups like groupBy, but based on a function which says whether 2 elements are consecutive
consecutiveBy                  :: (a -> a -> Bool) -> [a] -> [[a]]
consecutiveBy _        []      =  []
consecutiveBy isConsec (x:xs)  =  ys : consecutiveBy isConsec zs
  where (ys,zs) = consec x xs
        consec x []                        = ([x],[])
        consec x yys@(y:ys) | isConsec x y = let (yys',zs) = consec y ys in (x:yys',zs)
                            | otherwise    = ([x],yys)

-- | Partition on part of something, yielding a something else in the partitioning
partitionOnSplit :: (a -> (x,y)) -> (x -> x') -> (x -> Bool) -> [a] -> ([(x',y)],[y])
partitionOnSplit split adapt pred xs = foldr sel ([],[]) xs
  where sel x ~(ts,fs) | pred x'   = ((adapt x',y):ts,   fs)
                       | otherwise = (             ts, y:fs)
          where (x',y) = split x

{-
partition               :: (a -> Bool) -> [a] -> ([a],[a])
{-# INLINE partition #-}
partition p xs = foldr (select p) ([],[]) xs

select :: (a -> Bool) -> a -> ([a], [a]) -> ([a], [a])
select p x ~(ts,fs) | p x       = (x:ts,fs)
                    | otherwise = (ts, x:fs)
-}

-------------------------------------------------------------------------
-- Partitioning with rebuild
-------------------------------------------------------------------------

-- | Partition, but also return a function which will rebuild according to the original ordering of list elements
partitionAndRebuild :: (v -> Bool) -> [v] -> ([v], [v], [v'] -> [v'] -> [v'])
partitionAndRebuild f (v:vs)
  | f v                  = (v : vs1,     vs2, \(r:r1)   r2  -> r : mk r1 r2)
  | otherwise            = (    vs1, v : vs2, \   r1 (r:r2) -> r : mk r1 r2)
  where (vs1,vs2,mk) = partitionAndRebuild f vs
partitionAndRebuild _ [] = ([], [], \_ _ -> [])

-------------------------------------------------------------------------
-- Ordering
-------------------------------------------------------------------------

{-
-- | Reduce compare results lexicographically to one compare result
orderingLexicList :: [Ordering] -> Ordering
orderingLexicList = foldr1 orderingLexic
{-# INLINE orderingLexicList #-}

-- | Reduce compare results lexicographically using a continuation ordering
orderingLexic :: Ordering -> Ordering -> Ordering
orderingLexic o1 o2 = if o1 == EQ then o2 else o1
{-# INLINE orderingLexic #-}
-}

-------------------------------------------------------------------------
-- Maybe
-------------------------------------------------------------------------

{-
panicJust :: String -> Maybe a -> a
panicJust m = maybe (panic m) id
{-# INLINE panicJust #-}
-}

infixr 0  $?

($?) :: (a -> Maybe b) -> Maybe a -> Maybe b
f $? mx = do x <- mx
             f x

orMb :: Maybe a -> Maybe a -> Maybe a
orMb m1 m2 = maybe m2 (const m1) m1
-- orMb = maybeOr Nothing Just Just

maybeAnd :: x -> (a -> b -> x) -> Maybe a -> Maybe b -> x
maybeAnd n jj ma mb
  = case ma of
      Just a
        -> case mb of {Just b -> jj a b ; _ -> n}
      _ -> n

maybeOr :: x -> (a -> x) -> (b -> x) -> Maybe a -> Maybe b -> x
maybeOr n fa fb ma mb
  = case ma of
      Just a -> fa a
      _      -> case mb of
                  Just b -> fb b
                  _      -> n

-------------------------------------------------------------------------
-- Strongly Connected Components
-------------------------------------------------------------------------

scc :: Ord n => [(n,[n])] -> [[n]]
scc = map Graph.flattenSCC . Graph.stronglyConnComp . map (\(n,ns) -> (n, n, ns))

-------------------------------------------------------------------------
-- Map
-------------------------------------------------------------------------

-- | double lookup, with transformer for 2nd map
mapLookup2' :: (Ord k1, Ord k2) => (v1 -> Map.Map k2 v2) -> k1 -> k2 -> Map.Map k1 v1 -> Maybe (Map.Map k2 v2, v2)
mapLookup2' f k1 k2 m1
  = do m2 <- Map.lookup k1 m1
       let m2' = f m2
       fmap ((,) m2') $ Map.lookup k2 m2'

-- | double lookup
mapLookup2 :: (Ord k1, Ord k2) => k1 -> k2 -> Map.Map k1 (Map.Map k2 v2) -> Maybe v2
mapLookup2 k1 k2 m1 = fmap snd $ mapLookup2' id k1 k2 m1
{-# INLINE mapLookup2 #-}

-------------------------------------------------------------------------
-- Monad
-------------------------------------------------------------------------

-- | loop over monads yielding a Maybe from a start value, yielding the first Just or the start (when no Just is returned)
firstMaybeM :: Monad m => a -> [a -> m (Maybe a)] -> m a
firstMaybeM x []     = return x
firstMaybeM x (s:ss) = do mx <- s x
                          maybe (firstMaybeM x ss) return mx

-- | Monadic equivalent of break: evaluate monads until a predicate is True, returning what is yes/no evaluated and the split point
breakM :: Monad m => (a -> Bool) -> [m a] -> m ([a], Maybe (a,[m a]))
breakM p l = br [] l >>= \(acc,res) -> return (reverse acc, res)
  where br acc []     = return (acc, Nothing)
        br acc (m:ms) = m >>= \x -> if p x then return (acc, Just (x, ms)) else br (x:acc) ms
