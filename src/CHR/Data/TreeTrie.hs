{-# LANGUAGE CPP, ScopedTypeVariables, StandaloneDeriving, TypeFamilies, MultiParamTypeClasses, PatternGuards, GADTs #-}

-------------------------------------------------------------------------------------------
--- TreeTrie, variation which allows matching on subtrees marked as a variable (kind of unification)
-------------------------------------------------------------------------------------------

{- |
A TreeTrie is a search structure where the key actually consists of a
tree of keys, represented as a list of layers in the tree, 1 for every
depth, starting at the top, which are iteratively used for searching.
The search structure for common path/prefixes is shared, the trie
branches to multiple corresponding to available children, length
equality of children is used in searching (should match)

The TreeTrie structure implemented in this module deviates from the
usual TreeTrie implementations in that it allows wildcard matches
besides the normal full match. The objective is to also be able to
retrieve values for which (at insertion time) it has been indicated that
part does not need full matching. This intentionally is similar to
unification, where matching on a variable will succeed for arbitrary
values. Unification is not the job of this TreeTrie implementation, but
by returning partial matches as well, a list of possible match
candidates is returned.
-}

module CHR.Data.TreeTrie
  ( -- * Key into TreeTrie
    PreKey1
  -- , PreKey1Cont(..)
  {-
    TreeTrie1Key(..)
  , TreeTrieMp1Key(..)
  , TreeTrieMpKey
  -}
  , Key
  
  {-
  , TrTrKey
  
  , ppTreeTrieKey
  
  , ttkSingleton
  , ttkAdd', ttkAdd
  , ttkChildren
  , ttkFixate
  
  , ttkParentChildren
  -}
    -- * Keyable
  , TrTrKey
  , TreeTrieKeyable(..)
  , toTreeTrieKey
  
  , prekey1
  , prekey1Wild
  , prekey1Nil
  , prekey1Delegate
  , prekey1WithChildren
  , prekey1With2Children
  , prekey1WithChild
  
    -- * TreeTrie
  , TreeTrie
  , emptyTreeTrie
  , empty
  , toListByKey, toList
  , fromListByKeyWith, fromList
  {-
  -}
  
    -- * Lookup
  , lookup
  , lookupResultToList
    -- * Properties/observations
  , isEmpty, null
  -- , elems
  
    -- * Construction
  , singleton, singletonKeyable
  , unionWith, union, unionsWith, unions
  , insertByKeyWith, insertByKey
  
  {-
    -- * Deletion
  , deleteByKey, delete
  , deleteListByKey
  -}
  )
  where

import           Prelude                    hiding (lookup,null)

import qualified Data.Set                   as Set
import qualified Data.Map                   as Map
import           Data.Maybe
import           Data.Monoid
import qualified Data.List                  as List
import           Data.Typeable(Typeable)

import           GHC.Generics

import           Control.Monad

import           CHR.Utils

-- import           UHC.Util.Serialize
-- import           UHC.Util.Pretty            hiding (empty)
-- import qualified UHC.Util.Pretty            as PP
-- import           UHC.Util.AssocL
import qualified CHR.Data.FastSeq           as Seq

-------------------------------------------------------------------------------------------
--- Key AST, used to index into TreeTrie
-------------------------------------------------------------------------------------------

-- | Key used on 1 level of trie.
-- Key1_Wild plays a special role, may occur in Key1_Multi only, and in there it is guaranteed to have non wild siblings, allowing easy wildcard lookup where only not all elements of the group need be a specific Key1_Single
data Key1 k
  = Key1_Single k
  | Key1_Multi  [Key1 k]
  | Key1_Wild                   -- ^ equal to anything
  | Key1_Nil                    -- ^ equal to nothing, except Key1_Wild
  deriving (Generic, Typeable {-, Eq, Ord -})

instance Functor Key1 where
  fmap f (Key1_Single k) = Key1_Single $ f k
  fmap f (Key1_Multi ks) = Key1_Multi  $ map (fmap f) ks
  fmap _ Key1_Wild       = Key1_Wild
  fmap _ Key1_Nil        = Key1_Nil

{-
-}
instance Eq k => Eq (Key1 k) where
  Key1_Single k1 == Key1_Single k2 = k1  == k2
  Key1_Multi ks1 == Key1_Multi ks2 = ks1 == ks2
  Key1_Nil       == Key1_Nil       = True
  Key1_Wild      == _              = True
  _              == Key1_Wild      = True
  _              == _              = False

instance Ord k => Ord (Key1 k) where
  Key1_Single k1 `compare` Key1_Single k2 = k1  `compare` k2
  Key1_Multi ks1 `compare` Key1_Multi ks2 = ks1 `compare` ks2
  Key1_Nil       `compare` Key1_Nil       = EQ
  Key1_Wild      `compare` _              = EQ
  _              `compare` Key1_Wild      = EQ
  Key1_Nil       `compare` _              = LT
  _              `compare` Key1_Nil       = GT
  Key1_Single _  `compare` _              = LT
  _              `compare` Key1_Single _  = GT

instance Show k => Show (Key1 k) where
  show (Key1_Single k) = "(" ++ show k ++ ")"
  show (Key1_Multi ks) = "[" ++ (concat $ List.intersperse "," $ map show ks) ++ "]"
  show  Key1_Wild      = "*"
  show  Key1_Nil       = "_"

{-
instance PP k => PP (Key1 k) where
  pp (Key1_Single k) = ppParens k
  pp (Key1_Multi ks) = ppBracketsCommas ks
  pp  Key1_Wild      = pp "*"
  pp  Key1_Nil       = pp "_"
-}

key1IsWild :: Key1 k -> Bool
key1IsWild Key1_Wild = True
key1IsWild _         = False
{-# INLINE key1IsWild #-}

-- | Full key
newtype Key k = Key {unKey :: [Key1 k]}
  deriving (Eq, Ord, Generic, Typeable, Show)

{-
instance PP k => PP (Key k) where
  pp = ppBracketsCommas . unKey
-}

-- | Simplify a generated raw Key1 into its canonical form used for indexing
key1RawToCanon :: Key1 k -> Key1 k
key1RawToCanon k = case k of
    Key1_Multi ks 
      | List.null ks  -> Key1_Nil
      | all iswld sks -> Key1_Wild
      | all issim sks -> Key1_Nil
      | [sk] <- sks   -> sk
      | otherwise     -> Key1_Multi sks
      where sks = map key1RawToCanon ks
    -- k | issimp k       -> Key1_Nil
    k                  -> k
  where -- issimp Key1_Wild = True
        isnil Key1_Nil  = True
        isnil _         = False
        iswld Key1_Wild = True
        iswld _         = False
        issim k         = isnil k || iswld k

-- | Simplify a generated raw Key into its canonical form used for indexing
keyRawToCanon :: Key k -> Key k
keyRawToCanon = Key . simp . unKey
  where simp ks = case ks of
          (k:ks) | Key1_Nil  <- kc -> []
                 | Key1_Wild <- kc -> [] -- [Key1_Wild] -- if only wild further subtree matching would succeed by def
                 | otherwise       -> kc : simp ks
            where kc = key1RawToCanon k
          _ -> []

-------------------------------------------------------------------------------------------
--- Keyable
-------------------------------------------------------------------------------------------

type family TrTrKey x :: *

type instance TrTrKey [x] = TrTrKey x

data PreKey1Cont y where
  PreKey1Cont_None :: PreKey1Cont y
  PreKey1Cont      :: (TrTrKey y ~ TrTrKey x, TreeTrieKeyable x) =>  x  -> PreKey1Cont y
  PreKey1Cont2     :: (TrTrKey y ~ TrTrKey x1, TrTrKey y ~ TrTrKey x2, TreeTrieKeyable x1, TreeTrieKeyable x2) =>  x1 -> x2  -> PreKey1Cont y
  PreKey1Conts     :: (TrTrKey y ~ TrTrKey x, TreeTrieKeyable x) => [x] -> PreKey1Cont y

data PreKey1 x
  = PreKey1       (TrTrKey x) (PreKey1Cont x)
  | PreKey1_Deleg             (PreKey1Cont x)
  | PreKey1_Wild
  | PreKey1_Nil
  
-- | Keyable values, i.e. capable of yielding a TreeTrieKey for retrieval from a trie
class TreeTrieKeyable x where
  toTreeTriePreKey1 :: x -> PreKey1 x

{-
instance TreeTrieKeyable (a,b) where
  toTreeTriePreKey1 (a,b) = PreKey1Cont2 a b
-}

toTreeTrieKey :: TreeTrieKeyable x => x -> Key (TrTrKey x)
toTreeTrieKey = keyRawToCanon . Key . mkx
  where nil   = repeat Key1_Nil
        mkx x = case toTreeTriePreKey1 x of
                  PreKey1 k     mbx -> Key1_Single k : cont mbx
                  PreKey1_Deleg mbx -> cont mbx
                  PreKey1_Wild      -> repeat Key1_Wild
                  PreKey1_Nil       -> nil
        cont :: PreKey1Cont y -> [Key1 (TrTrKey y)]
        cont c = case c of
          PreKey1Cont_None -> nil
          PreKey1Cont  x   -> mkx x
          PreKey1Cont2 x y -> zipWithN Key1_Multi [mkx x, mkx y]
          PreKey1Conts xs  -> zipWithN Key1_Multi $ map mkx xs

-- | Single key
prekey1 :: TrTrKey x -> PreKey1 x
prekey1 k = PreKey1 k PreKey1Cont_None

-- | Wildcard, matching anything
prekey1Wild :: PreKey1 x
prekey1Wild = PreKey1_Wild

-- | No key
prekey1Nil :: PreKey1 x
prekey1Nil = PreKey1_Nil

-- | No key, delegate to next layer
prekey1Delegate :: (TrTrKey y ~ TrTrKey x, TreeTrieKeyable y) => y -> PreKey1 x
prekey1Delegate c = PreKey1_Deleg (PreKey1Cont c)

-- | Key with single child
prekey1WithChild :: (TrTrKey y ~ TrTrKey x, TreeTrieKeyable y) => TrTrKey x -> y -> PreKey1 x
prekey1WithChild k c = PreKey1 k (PreKey1Cont c)

-- | Key with children
prekey1WithChildren :: (TrTrKey y ~ TrTrKey x, TreeTrieKeyable y) => TrTrKey x -> [y] -> PreKey1 x
prekey1WithChildren k cs = PreKey1 k (PreKey1Conts cs)

-- | Key with 2 children
prekey1With2Children :: (TrTrKey y1 ~ TrTrKey x, TrTrKey y2 ~ TrTrKey x, TreeTrieKeyable y1, TreeTrieKeyable y2) => TrTrKey x -> y1 -> y2 -> PreKey1 x
prekey1With2Children k c1 c2 = PreKey1 k (PreKey1Cont2 c1 c2)

-------------------------------------------------------------------------------------------
--- TreeTrie structure
-------------------------------------------------------------------------------------------

-- | Child structure
type TreeTrieChildren k v
  = Map.Map (Key1 k) (TreeTrie k v)

-- | The trie structure, branching out on (1) kind, (2) nr of children, (3) actual key
data TreeTrie k v
  = TreeTrie
      { ttrieMbVal       :: Maybe v                                                 -- value
      , ttrieSubs        :: TreeTrieChildren k v                                    -- children
      }
 deriving (Typeable)

emptyTreeTrie, empty :: TreeTrie k v
emptyTreeTrie = TreeTrie Nothing Map.empty

empty = emptyTreeTrie

instance (Show k, Show v) => Show (TreeTrie k v) where
  showsPrec _ t = showList $ toListByKey t

{-
instance (PP k, PP v) => PP (TreeTrie k v) where
  pp t = ppBracketsCommasBlock $ map (\(a,b) -> a >#< ":" >#< b) $ toListByKey t
-}

-------------------------------------------------------------------------------------------
--- Conversion
-------------------------------------------------------------------------------------------

-- Reconstruction of original key-value pairs.

toFastSeqSubsWith :: (Key k -> v -> v') -> TreeTrieChildren k v -> Seq.FastSeq v'
toFastSeqSubsWith mk ttries
  = mconcat
      [ toFastSeqWith (\(Key ks) v -> mk (Key $ k:ks) v) True t
      | (k,t) <- Map.toList ttries
      ]

toFastSeqSubs :: TreeTrieChildren k v -> Seq.FastSeq (Key k, v)
toFastSeqSubs = toFastSeqSubsWith (,)
{-
toFastSeqSubs ttries
  = mconcat
      [ Seq.map (\(Key ks,v) -> (Key $ k:ks, v)) $ toFastSeq True t
      | (k,t) <- Map.toList ttries
      ]
-}

toFastSeqWith :: (Key k -> v -> v') -> Bool -> TreeTrie k v -> Seq.FastSeq v'
toFastSeqWith mk inclEmpty ttrie
  =           (case ttrieMbVal ttrie of
                 Just v | inclEmpty -> Seq.singleton $ mk (Key []) v
                 _                  -> Seq.empty
              )
    `mappend` toFastSeqSubsWith mk (ttrieSubs ttrie)

toFastSeq :: Bool -> TreeTrie k v -> Seq.FastSeq (Key k, v)
toFastSeq = toFastSeqWith (,)
{-
toFastSeq inclEmpty ttrie
  =           (case ttrieMbVal ttrie of
                 Just v | inclEmpty -> Seq.singleton (Key [], v)
                 _                  -> Seq.empty
              )
    `mappend` toFastSeqSubs (ttrieSubs ttrie)
-}

toListByKey, toList :: TreeTrie k v -> [(Key k,v)]
toListByKey = Seq.toList . toFastSeq True

toList = toListByKey

fromListByKeyWith :: Ord k => (v -> v -> v) -> [(Key k,v)] -> TreeTrie k v
fromListByKeyWith cmb = unionsWith cmb . map (uncurry singleton)

fromListByKey :: Ord k => [(Key k,v)] -> TreeTrie k v
fromListByKey = unions . map (uncurry singleton)

fromListWith :: Ord k => (v -> v -> v) -> [(Key k,v)] -> TreeTrie k v
fromListWith cmb = fromListByKeyWith cmb

fromList :: Ord k => [(Key k,v)] -> TreeTrie k v
fromList = fromListByKey

-------------------------------------------------------------------------------------------
--- Lookup
-------------------------------------------------------------------------------------------

type LkRes v = (Seq.FastSeq v, Seq.FastSeq v, Maybe v)

-- | Lookup giving back possible precise result and values found whilst descending into trie (corresponding to wildcard in key in trie) and remaining when key is exhausted (corresponding to wildcard in key)
lookupWith :: Ord k => (Key k -> v -> v') -> Key k -> TreeTrie k v -> LkRes v'
lookupWith mkRes keys ttrie = case unKey keys of
    [] -> (mempty, toFastSeqWith mkRes True ttrie, fmap (mkRes $ Key []) $ ttrieMbVal ttrie)
    (k : ks)
       -> case Map.lookup k $ ttrieSubs ttrie of
            Just ttrie'
              -> (pp `mappend` p, s, m)
              where (p, s, m) = lookupWith (\(Key ks) v -> mkRes (Key (k : ks)) v) (Key ks) ttrie'
            _ -> (pp, mempty, Nothing)
       where pp = maybe mempty (Seq.singleton . mkRes (Key [])) (ttrieMbVal ttrie)

-- | Lookup giving back possible precise result and values found whilst descending into trie (corresponding to wildcard in key in trie) and remaining when key is exhausted (corresponding to wildcard in key)
lookup :: Ord k => Key k -> TreeTrie k v -> LkRes v
lookup = lookupWith $ \_ v -> v

{-

lookupPartialByKey :: (PP k,Ord k) => TreeTrieLookup -> TreeTrieKey k -> TreeTrie k v -> ([v],Maybe v)
lookupPartialByKey = lookupPartialByKey' (\_ v -> v)

lookupByKey, lookup :: (PP k,Ord k) => TreeTrieKey k -> TreeTrie k v -> Maybe v
lookupByKey keys ttrie = snd $ lookupPartialByKey TTL_WildInTrie keys ttrie

lookup = lookupByKey
-}

-- | Convert the lookup result to a list of results
lookupResultToList :: LkRes v -> [v]
lookupResultToList (p,s,mv) = maybeToList mv ++ Seq.toList (p `mappend` s)


-------------------------------------------------------------------------------------------
--- Observation
-------------------------------------------------------------------------------------------


isEmpty :: TreeTrie k v -> Bool
isEmpty ttrie
  =  isNothing (ttrieMbVal ttrie)
  && Map.null  (ttrieSubs ttrie)

null :: TreeTrie k v -> Bool
null = isEmpty

{-
elems :: TreeTrie k v -> [v]
elems = map snd . toListByKey
-}

-------------------------------------------------------------------------------------------
--- Construction
-------------------------------------------------------------------------------------------

singleton :: Ord k => Key k -> v -> TreeTrie k v
singleton (Key keys) val
  = s keys
  where s []       = TreeTrie (Just val) Map.empty
        s (k : ks) = TreeTrie Nothing (Map.singleton k $ singleton (Key ks) val) 

singletonKeyable :: (Ord (TrTrKey v),TreeTrieKeyable v) => v -> TreeTrie (TrTrKey v) v
singletonKeyable val = singleton (toTreeTrieKey val) val

-------------------------------------------------------------------------------------------
--- Union, insert, ...
-------------------------------------------------------------------------------------------

unionWith :: Ord k => (v -> v -> v) -> TreeTrie k v -> TreeTrie k v -> TreeTrie k v
unionWith cmb t1 t2
  = TreeTrie
      { ttrieMbVal       = mkMb          cmb             (ttrieMbVal t1) (ttrieMbVal t2)
      , ttrieSubs        = Map.unionWith (unionWith cmb) (ttrieSubs  t1) (ttrieSubs  t2)
      }
  where mkMb _   j         Nothing   = j
        mkMb _   Nothing   j         = j
        mkMb cmb (Just x1) (Just x2) = Just $ cmb x1 x2

union :: Ord k => TreeTrie k v -> TreeTrie k v -> TreeTrie k v
union = unionWith const

unionsWith :: Ord k => (v -> v -> v) -> [TreeTrie k v] -> TreeTrie k v
unionsWith cmb [] = emptyTreeTrie
unionsWith cmb ts = foldr1 (unionWith cmb) ts

unions :: Ord k => [TreeTrie k v] -> TreeTrie k v
unions = unionsWith const

insertByKeyWith :: Ord k => (v -> v -> v) -> Key k -> v -> TreeTrie k v -> TreeTrie k v
insertByKeyWith cmb keys val ttrie = unionsWith cmb [singleton keys val,ttrie]

insertByKey :: Ord k => Key k -> v -> TreeTrie k v -> TreeTrie k v
insertByKey = insertByKeyWith const

insert :: Ord k => Key k -> v -> TreeTrie k v -> TreeTrie k v
insert = insertByKey

insertKeyable :: (Ord (TrTrKey v),TreeTrieKeyable v) => v -> TreeTrie (TrTrKey v) v -> TreeTrie (TrTrKey v) v
insertKeyable val = insertByKey (toTreeTrieKey val) val

-------------------------------------------------------------------------------------------
--- Delete, ...
-------------------------------------------------------------------------------------------

{-

deleteByKey, delete :: Ord k => TreeTrieKey k -> TreeTrie k v -> TreeTrie k v
deleteByKey (TreeTrieKey keys) ttrie
  = d keys ttrie
  where d [] t
          = t {ttrieMbVal = Nothing}
        d (k : ks) t
          = case fmap (d ks) $ Map.lookup k $ ttrieSubs t of
              Just c | isEmpty c -> t { ttrieSubs = k `Map.delete` ttrieSubs t }
                     | otherwise -> t { ttrieSubs = Map.insert k c $ ttrieSubs t }
              _                  -> t

delete = deleteByKey

deleteListByKey :: Ord k => [TreeTrieKey k] -> TreeTrie k v -> TreeTrie k v
deleteListByKey keys ttrie = foldl (\t k -> deleteByKey k t) ttrie keys

-}

-------------------------------------------------------------------------------------------
--- Instances: Serialize
-------------------------------------------------------------------------------------------

{-
instance (Ord k, Serialize k, Serialize v) => Serialize (TreeTrie k v) where
  sput (TreeTrie a b) = sput a >> sput b
  sget = liftM2 TreeTrie sget sget
  
instance (Serialize k) => Serialize (Key k) where
  sput (Key a) = sput a
  sget = liftM Key sget
  
instance (Serialize k) => Serialize (Key1 k)
-}

-------------------------------------------------------------------------------------------
--- Test
-------------------------------------------------------------------------------------------

{-
test1
  = fromListByKey
      [ ( TreeTrieKey
          [ TreeTrieMpKey [TTM1K [TT1K_One "C"]]
          , TreeTrieMpKey [TTM1K [TT1K_Any, TT1K_One "P"]]
          , TreeTrieMpKey [TTM1K [TT1K_One "D", TT1K_One "F"], TTM1K []]
          ] 
        , "C (* D F) P" 
        ) 
      , ( TreeTrieKey 
          [ TreeTrieMpKey [TTM1K [TT1K_One "C"]]
          , TreeTrieMpKey [TTM1K [TT1K_One "B", TT1K_One "P"]]
          , TreeTrieMpKey [TTM1K [TT1K_One "D", TT1K_One "F"], TTM1K []]
          ]
        , "C (B D F) P"
        )
      , ( TreeTrieKey
          [ TreeTrieMpKey [TTM1K [TT1K_One "C"]]
          , TreeTrieMpKey [TTM1K [TT1K_One "B", TT1K_One "P"]]
          , TreeTrieMpKey [TTM1K [], TTM1K [TT1K_One "Q", TT1K_One "R"]]
          ]
        , "C B (P Q R)"
        )
      , ( TreeTrieKey
          [ TreeTrieMpKey [TTM1K [TT1K_One "C"]]
          , TreeTrieMpKey [TTM1K [TT1K_One "B", TT1K_Any]]
          ]
        , "C B *"
        )
      ]

t1k1 = TreeTrieKey
          [ TreeTrieMpKey [TTM1K [TT1K_One "C"]]
          , TreeTrieMpKey [TTM1K [TT1K_Any, TT1K_One "P"]]
          , TreeTrieMpKey [TTM1K [TT1K_One "D", TT1K_One "F"], TTM1K []]
          ]
-}

{-
m1 = fromJust 
     $ fmap (\f -> f $ [TTM1K [], TTM1K [TT1K_One "Z"]])
     $ matchTreeTrieMpKeyTo
        [TTM1K [TT1K_Any, TT1K_One "P"]]
        [TTM1K [TT1K_One "B", TT1K_One "P"]]

m2 = fmap (\f -> f $ repeat (TTM1K []))
     $ matchTreeTrieMpKeyTo
        m1
        [TTM1K [TT1K_One "D", TT1K_One "F"], TTM1K [TT1K_One "Z"]]

m3 = fromJust 
     $ fmap (\f -> f $ [TTM1K [TT1K_Any, TT1K_One "P"]])
     $ matchTreeTrieMpKeyTo
        [TTM1K [TT1K_One "C"]]
        [TTM1K [TT1K_One "C"]]

m4 = fmap (\f -> f $ repeat (TTM1K []))
     $ matchTreeTrieMpKeyTo
        m3
        [TTM1K [TT1K_One "B", TT1K_One "P"]]

m5 = fmap (\f -> f $ repeat (TTM1K []))
     $ matchTreeTrieMpKeyTo
        (fromJust m4)
        [TTM1K [TT1K_One "D", TT1K_One "F"], TTM1K []]

l1t1 = lookupPartialByKey' (,) TTL_Exact
          [ [TTM1K [TT1K_One "C"]]
          , [TTM1K [TT1K_Any, TT1K_One "P"]]
          ]

l2t1 = lookupPartialByKey' (,) TTL_WildInTrie
          [ [TTM1K [TT1K_One "C"]]
          , [TTM1K [TT1K_One "B", TT1K_One "P"]]
          ]

l3t1 = lookupPartialByKey' (,) TTL_WildInKey
          [ [TTM1K [TT1K_One "C"]]
          , [TTM1K [TT1K_Any, TT1K_One "P"]]
          ]

l4t1 = lookupPartialByKey' (,) TTL_WildInKey
          [ [TTM1K [TT1K_Any :: TreeTrie1Key String]]
          ]

l5t1 = lookupPartialByKey' (,) TTL_WildInTrie
          [ [TTM1K [TT1K_One "C"]]
          , [TTM1K [TT1K_One "B", TT1K_One "P"]]
          , [TTM1K [TT1K_One "D", TT1K_One "F"], TTM1K []]
          ]

l6t1 = lookupPartialByKey' (,) TTL_WildInKey
          [ [TTM1K [TT1K_One "C"]]
          , [TTM1K [TT1K_Any, TT1K_One "P"]]
          , [TTM1K [TT1K_One "D", TT1K_One "F"], TTM1K []]
          ]

-}

{-

          , [<[1:S:Prf]>,<[1:S:occ]>,<[*,1:S:\]>,<[],[*]>]
              : [ Prove (m_10_0\l_12_0,<sc_1_0>,??)
                  ==>
                  (m_10_0 == (m_11_0 | ...)) \ l_12_0@off_13_0
                  | [ Prove (m_11_0\l_12_0,<sc_1_0>,??)
                    , Red (m_10_0\l_12_0,<sc_1_0>,??) < label l_12_0@off_13_0<sc_1_0> < [(m_11_0\l_12_0,<sc_1_0>,??)]]
                , Prove ({||}\l_12_0,<sc_1_0>,??)
                  ==>
                  Red ({||}\l_12_0,<sc_1_0>,??) < label l_12_0@0<sc_1_0> < []]

        [<[1:S:Prf]>,<[1:S:occ]>,<[1:S:[0,0],1:S:\]>,<[],[1:H:3]>,<[1:U:3_48_0_0,1:U:3_48_0_1]>]: 1

-}

{-
test2
  = fromListByKey
      [ ( [ [TTM1K [TT1K_One "P"]]
          , [TTM1K [TT1K_One "O"]]
          , [TTM1K [TT1K_Any, TT1K_One "SL"]]
          , [TTM1K [], TTM1K [TT1K_Any]]
          ]
        , "P (O * (SL *))"
        )
      ]

l1t2 = lookupPartialByKey' (,) TTL_WildInTrie
          [ [TTM1K [TT1K_One "P"]]
          , [TTM1K [TT1K_One "O"]]
          , [TTM1K [TT1K_One "Sc", TT1K_One "SL"]]
          , [TTM1K [], TTM1K [TT1K_One "3"]]
          , [TTM1K [TT1K_One "3_48_0_0", TT1K_One "3_48_0_1"]]
          ]

-}

{-
test3
  = fromListByKey
      [ ( [[TTM1K [TT1K_One "1:S:Prf"]]
          ,[TTM1K [TT1K_One "1:S:occ"]]
          ,[TTM1K [TT1K_Any, TT1K_One "1:H:Language.UHC.JS.ECMA.Types.ToJS"]]
          ,[TTM1K [], TTM1K [TT1K_One "1:H:UHC.Base.Maybe",TT1K_Any]]
          ,[TTM1K [TT1K_Any], TTM1K []]
          ]
        , "xx"
        )
      ]

l1t3 = lookupPartialByKey' (,) TTL_WildInTrie
        [[TTM1K [TT1K_One "1:S:Prf"]]
        ,[TTM1K [TT1K_One "1:S:occ"]]
        ,[TTM1K [TT1K_One "1:S:[0,0,0,0,0,0]", TT1K_One "1:H:Language.UHC.JS.ECMA.Types.ToJS"]]
        ,[TTM1K [],TTM1K [TT1K_One "1:H:UHC.Base.Maybe", TT1K_One "1:H:Language.UHC.JS.ECMA.Types.JSAny"]]
        ,[TTM1K [TT1K_One "1:H:Language.UHC.JS.ECMA.Types.JSAny"], TTM1K [TT1K_One "1:U:12_398_1_0"]]
        ,[TTM1K [TT1K_One "1:H:Language.UHC.JS.ECMA.Types.JSObject_"], TTM1K []]
        ,[TTM1K [TT1K_One "1:H:Language.UHC.JS.W3C.HTML5.NodePtr"]]
        ]

          

-}

{-
  , [<[1:S:Prf]>
    ,<[1:S:occ]>
    ,<[*,1:H:Language.UHC.JS.ECMA.Types.ToJS]>
    ,<[],[1:H:UHC.Base.Maybe,*]>
    ,<[*],[]>
    ]

, DBG lookups for
  [<[1:S:Prf]>
  ,<[1:S:occ]>
  ,<[1:S:[0,0,0,0,0,0],1:H:Language.UHC.JS.ECMA.Types.ToJS]>
  ,<[],[1:H:UHC.Base.Maybe,1:H:Language.UHC.JS.ECMA.Types.JSAny]>
  ,<[1:H:Language.UHC.JS.ECMA.Types.JSAny],[1:U:12_398_1_0]>
  ,<[1:H:Language.UHC.JS.ECMA.Types.JSObject_],[]>
  ,<[1:H:Language.UHC.JS.W3C.HTML5.NodePtr]>
  ]

-}

-------------------------------------------------------------------------------------------
--- Key into TreeTrie
-------------------------------------------------------------------------------------------

{-
-- | Both key and trie can allow partial matching, indicated by TreeTrie1Key
data TreeTrie1Key k
  = TT1K_One    !k
  | TT1K_Any                            -- used to wildcard match a single node in a tree
  deriving (Eq, Ord, Generic)

-- | A key in a layer of TreeTrieMpKey
data TreeTrieMp1Key k
  = TTM1K       ![TreeTrie1Key k]
  | TTM1K_Any                           -- used to wildcard match multiple children, internal only
  deriving (Eq, Ord, Generic)

-- | The key into a map used internally by the trie
newtype TreeTrieMpKey k
  = TreeTrieMpKey {unTreeTrieMpKey :: [TreeTrieMp1Key k]}
  deriving (Eq, Ord, Generic)

-- | The key used externally to index into a trie
newtype TreeTrieKey k
  = TreeTrieKey {unTreeTrieKey :: [TreeTrieMpKey k]}
  deriving (Eq, Ord, Generic)

#if __GLASGOW_HASKELL__ >= 708
deriving instance Typeable  TreeTrie1Key
deriving instance Typeable  TreeTrieMp1Key
#else
deriving instance Typeable1 TreeTrie1Key
deriving instance Typeable1 TreeTrieMp1Key
#endif
-- deriving instance Data x => Data (TreeTrie1Key x) 
-- deriving instance Data x => Data (TreeTrieMp1Key x) 

instance Show k => Show (TreeTrie1Key k) where
  show  TT1K_Any    = "*"
  show (TT1K_One k) = "(1:" ++ show k ++ ")"

instance Show k => Show (TreeTrieMp1Key k) where
  show (TTM1K_Any )  = "**" -- ++ show i
  show (TTM1K k)     = show k

instance PP k => PP (TreeTrie1Key k) where
  pp  TT1K_Any    = pp "*"
  pp (TT1K_One k) = ppParens $ "1:" >|< k

instance PP k => PP (TreeTrieMp1Key k) where
  pp = ppTreeTrieMp1Key

ppTreeTrieMp1Key :: PP k => TreeTrieMp1Key k -> PP_Doc
ppTreeTrieMp1Key (TTM1K l) = ppBracketsCommas l
ppTreeTrieMp1Key (TTM1K_Any ) = pp "**" -- >|< i

ppTreeTrieMpKey :: PP k => TreeTrieMpKey k -> PP_Doc
ppTreeTrieMpKey = ppListSep "<" ">" "," . map ppTreeTrieMp1Key . unTreeTrieMpKey

-- | Pretty print TrieKey
ppTreeTrieKey :: PP k => TreeTrieKey k -> PP_Doc
ppTreeTrieKey = ppBracketsCommas . map ppTreeTrieMpKey . unTreeTrieKey

instance Show k => Show (TreeTrieMpKey k) where
  show (TreeTrieMpKey ks) = show ks

instance Show k => Show (TreeTrieKey k) where
  show (TreeTrieKey ks) = show ks

instance PP k => PP (TreeTrieMpKey k) where
  pp = ppTreeTrieMpKey
  {-# INLINE pp #-}

instance PP k => PP (TreeTrieKey k) where
  pp = ppTreeTrieKey
  {-# INLINE pp #-}

-}

-------------------------------------------------------------------------------------------
--- TreeTrieMpKey inductive construction from new node and children keys
-------------------------------------------------------------------------------------------

{-
-- | Make singleton, which should at end be stripped from bottom layer of empty TTM1K []
ttkSingleton :: TreeTrie1Key k -> TreeTrieKey k
ttkSingleton k = TreeTrieKey $ TreeTrieMpKey [TTM1K [k]] : unTreeTrieKey ttkEmpty

-- | empty key
ttkEmpty :: TreeTrieKey k
ttkEmpty = TreeTrieKey [TreeTrieMpKey [TTM1K []]]

-- | Construct intermediate structure for children for a new Key
--   length ks >= 2
ttkChildren :: [TreeTrieKey k] -> TreeTrieKey k
ttkChildren ks
  = TreeTrieKey $ map TreeTrieMpKey
    $ [TTM1K $ concat [k | TTM1K k <- flatten hs]]       -- first level children are put together in singleton list of list with all children
      : merge (split tls)                                 -- and the rest is just concatenated
  where (hs,tls) = split ks
        split = unzip . map ((\(h,t) -> (h, TreeTrieKey t)) . hdAndTl . unTreeTrieKey)
        merge (hs,[]) = [flatten hs]
        merge (hs,tls) = flatten hs : merge (split $ filter (not . List.null . unTreeTrieKey) tls)
        flatten = concatMap (\(TreeTrieMpKey h) -> h)

-- | Add a new layer with single node on top, combining the rest.
ttkAdd' :: TreeTrie1Key k -> TreeTrieKey k -> TreeTrieKey k
ttkAdd' k (TreeTrieKey ks) = TreeTrieKey $ TreeTrieMpKey [TTM1K [k]] : ks

-- | Add a new layer with single node on top, combining the rest.
--   length ks >= 2
ttkAdd :: TreeTrie1Key k -> [TreeTrieKey k] -> TreeTrieKey k
ttkAdd k ks = ttkAdd' k (ttkChildren ks)

-- | Fixate by removing lowest layer empty children
ttkFixate :: TreeTrieKey k -> TreeTrieKey k
ttkFixate (TreeTrieKey (kk : kks))
  | all (\(TTM1K k) -> List.null k) (unTreeTrieMpKey kk)
              = TreeTrieKey []
  | otherwise = TreeTrieKey $ kk : unTreeTrieKey (ttkFixate $ TreeTrieKey kks)
ttkFixate _   = TreeTrieKey []
-}

-------------------------------------------------------------------------------------------
--- TreeTrieKey deconstruction
-------------------------------------------------------------------------------------------

{-
-- | Split key into parent and children components, inverse of ttkAdd'
ttkParentChildren :: TreeTrieKey k -> ( TreeTrie1Key k, TreeTrieKey k )
ttkParentChildren (TreeTrieKey k)
  = case k of
      (TreeTrieMpKey [TTM1K [h]] : t) -> (h, TreeTrieKey t)
-}

-------------------------------------------------------------------------------------------
--- TreeTrieMpKey matching
-------------------------------------------------------------------------------------------

{-
-- | Match 1st arg with wildcards to second, returning the to be propagated key to next layer in tree
matchTreeTrieMpKeyTo :: Eq k => TreeTrieMpKey k -> TreeTrieMpKey k -> Maybe (TreeTrieMpKey k -> TreeTrieMpKey k)
matchTreeTrieMpKeyTo (TreeTrieMpKey l) (TreeTrieMpKey r)
  | all isJust llrr = Just (\(TreeTrieMpKey k) -> TreeTrieMpKey $ concat $ zipWith ($) (concatMap (fromJust) llrr) k)
  | otherwise       = Nothing
  where llrr = zipWith m l r
        m (TTM1K     l) (TTM1K r) | length l == length r && all isJust lr
                                                  = Just (concatMap fromJust lr)
                                  | otherwise     = Nothing
                                  where lr = zipWith m1 l r
        m (TTM1K_Any  ) (TTM1K []) = Just []
        m (TTM1K_Any  ) (TTM1K r ) = Just [const $ replicate (length r) TTM1K_Any]
        m1  TT1K_Any     _                    = Just [const [TTM1K_Any]]
        m1 (TT1K_One l) (TT1K_One r) | l == r = Just [\x -> [x]]
        m1  _            _                    = Nothing
-}

