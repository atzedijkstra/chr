{-# LANGUAGE CPP, ScopedTypeVariables, StandaloneDeriving, TypeFamilies, MultiParamTypeClasses #-}

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

module UHC.Util.TreeTrie
  ( -- * Key into TreeTrie
    TreeTrie1Key(..)
  , TreeTrieMp1Key(..)
  , TreeTrieMpKey
  , TreeTrieKey
  
  , TrTrKey
  
  , ppTreeTrieKey
  
  , ttkSingleton
  , ttkAdd', ttkAdd
  , ttkChildren
  , ttkFixate
  
  , ttkParentChildren
  
    -- * Keyable
  , TreeTrieKeyable(..)
  
    -- * TreeTrie
  , TreeTrie
  , emptyTreeTrie
  , empty
  , toListByKey, toList
  , fromListByKeyWith, fromList

    -- * Lookup
  , TreeTrieLookup(..)
  
  , lookupPartialByKey
  , lookupPartialByKey'
  , lookupByKey
  , lookup
  , lookupResultToList

    -- * Properties/observations
  , isEmpty, null
  , elems
  
    -- * Construction
  , singleton, singletonKeyable
  , unionWith, union, unionsWith, unions
  , insertByKeyWith, insertByKey
  
    -- * Deletion
  , deleteByKey, delete
  , deleteListByKey
  )
  where

import           Data.Kind              (Type)
import qualified Data.Set as Set
import qualified Data.Map as Map
import           Data.Maybe
import           Prelude hiding (lookup,null)
import qualified UHC.Util.FastSeq as Seq
import qualified Data.List as List
import           UHC.Util.Utils
import           UHC.Util.Pretty hiding (empty)
import qualified UHC.Util.Pretty as PP
import           Control.Monad
import           Data.Typeable(Typeable)
-- import           Data.Generics(Data)
import           UHC.Util.Serialize

-------------------------------------------------------------------------------------------
--- Key into TreeTrie
-------------------------------------------------------------------------------------------

-- | Both key and trie can allow partial matching, indicated by TreeTrie1Key
data TreeTrie1Key k
  = TT1K_One    !k
  | TT1K_Any                            -- used to wildcard match a single node in a tree
  deriving (Eq, Ord)

-- | A key in a layer of TreeTrieMpKey
data TreeTrieMp1Key k
  = TTM1K       [TreeTrie1Key k]
  | TTM1K_Any                           -- used to wildcard match multiple children, internal only
  deriving (Eq, Ord)

-- | The key into a map used internally by the trie
type TreeTrieMpKey k
  = [TreeTrieMp1Key k]

-- | The key used externally to index into a trie
type TreeTrieKey k
  = [TreeTrieMpKey k]

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
ppTreeTrieMpKey = ppListSep "<" ">" "," . map ppTreeTrieMp1Key

-- | Pretty print TrieKey
ppTreeTrieKey :: PP k => TreeTrieKey k -> PP_Doc
ppTreeTrieKey = ppBracketsCommas . map ppTreeTrieMpKey


-------------------------------------------------------------------------------------------
--- TreeTrieMpKey inductive construction from new node and children keys
-------------------------------------------------------------------------------------------

-- | Make singleton, which should at end be stripped from bottom layer of empty TTM1K []
ttkSingleton :: TreeTrie1Key k -> TreeTrieKey k
ttkSingleton k = [TTM1K [k]] : ttkEmpty

-- | empty key
ttkEmpty :: TreeTrieKey k
ttkEmpty = [[TTM1K []]]

-- | Construct intermediate structure for children for a new Key
--   length ks >= 2
ttkChildren :: [TreeTrieKey k] -> TreeTrieKey k
ttkChildren ks
  =   [TTM1K $ concat [k | TTM1K k <- concat hs]]       -- first level children are put together in singleton list of list with all children
    : merge (split tls)                                 -- and the rest is just concatenated
  where (hs,tls) = split ks
        split = unzip . map hdAndTl
        merge (hs,[]) = [concat hs]
        merge (hs,tls) = concat hs : merge (split $ filter (not . List.null) tls)

-- | Add a new layer with single node on top, combining the rest.
ttkAdd' :: TreeTrie1Key k -> TreeTrieKey k -> TreeTrieKey k
ttkAdd' k ks = [TTM1K [k]] : ks

-- | Add a new layer with single node on top, combining the rest.
--   length ks >= 2
ttkAdd :: TreeTrie1Key k -> [TreeTrieKey k] -> TreeTrieKey k
ttkAdd k ks = ttkAdd' k (ttkChildren ks)

-- | Fixate by removing lowest layer empty children
ttkFixate :: TreeTrieKey k -> TreeTrieKey k
ttkFixate (kk:kks) | all (\(TTM1K k) -> List.null k) kk = []
                   | otherwise                          = kk : ttkFixate kks
ttkFixate _                                             = []

-------------------------------------------------------------------------------------------
--- TreeTrieKey deconstruction
-------------------------------------------------------------------------------------------

-- | Split key into parent and children components, inverse of ttkAdd'
ttkParentChildren :: TreeTrieKey k -> ( TreeTrie1Key k, TreeTrieKey k )
ttkParentChildren k
  = case k of
      ([TTM1K [h]] : t) -> (h,t)

-------------------------------------------------------------------------------------------
--- TreeTrieMpKey matching
-------------------------------------------------------------------------------------------

-- | Match 1st arg with wildcards to second, returning the to be propagated key to next layer in tree
matchTreeTrieMpKeyTo :: Eq k => TreeTrieMpKey k -> TreeTrieMpKey k -> Maybe (TreeTrieMpKey k -> TreeTrieMpKey k)
matchTreeTrieMpKeyTo l r
  | all isJust llrr = Just (\k -> concat $ zipWith ($) (concatMap (fromJust) llrr) k)
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

-------------------------------------------------------------------------------------------
--- Keyable
-------------------------------------------------------------------------------------------

type family TrTrKey x :: Type

-- | Keyable values, i.e. capable of yielding a TreeTrieKey for retrieval from a trie
class TreeTrieKeyable x where
  toTreeTrieKey :: x -> TreeTrieKey (TrTrKey x)

-------------------------------------------------------------------------------------------
--- TreeTrie structure
-------------------------------------------------------------------------------------------

-- | Child structure
type TreeTrieChildren k v
  = Map.Map (TreeTrieMpKey k) (TreeTrie k v)

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

{-
-- %%[9999 export(ppTreeTrieAsIs)
-- | PP a TreeTrie as is, directly corresponding to original structure
ppTreeTrieAsIs :: (PP k, PP v) => TreeTrie k v -> PP_Doc
ppTreeTrieAsIs t
  =     "V:" >#< (maybe PP.empty pp $ ttrieMbVal t)
    >-< "P:" >#< (ppSub $ ttriePartSubs t)
    >-< "N:" >#< (ppSub $ ttrieSubs t)
  where ppKV (k,v) = k >-< indent 2 (":" >#< ppTreeTrieAsIs v)
        ppSub = ppBracketsCommasBlock . map ppKV . Map.toList
-}

instance (Show k, Show v) => Show (TreeTrie k v) where
  showsPrec _ t = showList $ toListByKey t

instance (PP k, PP v) => PP (TreeTrie k v) where
  pp t = ppBracketsCommasBlock $ map (\(a,b) -> ppTreeTrieKey a >#< ":" >#< b) $ toListByKey t

-------------------------------------------------------------------------------------------
--- Conversion
-------------------------------------------------------------------------------------------

-- Reconstruction of original key-value pairs.

toFastSeqSubs :: TreeTrieChildren k v -> Seq.FastSeq (TreeTrieKey k,v)
toFastSeqSubs ttries
  = Seq.unions
      [ Seq.map (\(ks,v) -> (k:ks,v)) $ toFastSeq True t
      | (k,t) <- Map.toList ttries
      ]

toFastSeq :: Bool -> TreeTrie k v -> Seq.FastSeq (TreeTrieKey k,v)
toFastSeq inclEmpty ttrie
  =          (case ttrieMbVal ttrie of
                Just v | inclEmpty -> Seq.singleton ([],v)
                _                  -> Seq.empty
             )
    Seq.:++: toFastSeqSubs (ttrieSubs ttrie)

toListByKey, toList :: TreeTrie k v -> [(TreeTrieKey k,v)]
toListByKey = Seq.toList . toFastSeq True

toList = toListByKey

fromListByKeyWith :: Ord k => (v -> v -> v) -> [(TreeTrieKey k,v)] -> TreeTrie k v
fromListByKeyWith cmb = unionsWith cmb . map (uncurry singleton)

fromListByKey :: Ord k => [(TreeTrieKey k,v)] -> TreeTrie k v
fromListByKey = unions . map (uncurry singleton)

fromListWith :: Ord k => (v -> v -> v) -> [(TreeTrieKey k,v)] -> TreeTrie k v
fromListWith cmb = fromListByKeyWith cmb

fromList :: Ord k => [(TreeTrieKey k,v)] -> TreeTrie k v
fromList = fromListByKey

-------------------------------------------------------------------------------------------
--- TreeTrie lookup/insertion, how to
-------------------------------------------------------------------------------------------

-- | How to lookup in a TreeTrie
data TreeTrieLookup
  = TTL_Exact                           -- lookup with exact match
  | TTL_WildInTrie                      -- lookup with wildcard matching in trie
  | TTL_WildInKey                       -- lookup with wildcard matching in key
  deriving (Eq)

-------------------------------------------------------------------------------------------
--- Lookup
-------------------------------------------------------------------------------------------

-- | Normal lookup for exact match + partial matches (which require some sort of further unification, determining whether it was found)
lookupPartialByKey' :: forall k v v' . (PP k,Ord k) => (TreeTrieKey k -> v -> v') -> TreeTrieLookup -> TreeTrieKey k -> TreeTrie k v -> ([v'],Maybe v')
lookupPartialByKey' mkRes ttrieLookup keys ttrie
  = l id mkRes keys ttrie
  where l :: (TreeTrieMpKey k -> TreeTrieMpKey k) -> (TreeTrieKey k -> v -> v') -> TreeTrieKey k -> TreeTrie k v -> ([v'],Maybe v')
        l = case ttrieLookup of
              -- Exact match
              TTL_Exact -> \updTKey mkRes keys ttrie ->
                case keys of
                  [] -> dflt mkRes ttrie
                  (k : ks)
                     -> case Map.lookup k $ ttrieSubs ttrie of
                          Just ttrie'
                            -> ([], m)
                            where (_,m) = l id (res mkRes k) ks ttrie'
                          _ -> ([], Nothing)
              
              -- Match with possible wildcard in Trie
              TTL_WildInTrie -> \updTKey mkRes keys ttrie ->
                -- tr "TTL_WildInTrie" (ppTreeTrieKey keys >#< (ppTreeTrieMpKey $ updTKey $ replicate (5) (TTM1K []))) $
                case keys of
                  [] -> dflt mkRes ttrie
                  (k : ks)
                     -> (catMaybes mbs ++ concat subs, Nothing)
                     where (subs,mbs)
                             = unzip
                                 [ case ks of
                                     []                             -> l id (res mkRes k) [] t
                                     (_:_) | Map.null (ttrieSubs t) -> match (res mkRes k) (fromJust mbm) ks
                                           | otherwise              -> l (fromJust mbm) (res mkRes k) ks t
                                        where match mkRes m (km:kms)
                                                = case matchTreeTrieMpKeyTo kt' km of
                                                    Just m -> match (res mkRes k) m kms
                                                    _      -> ([], Nothing)
                                                where kt' = m $ repeat (TTM1K [])
                                              match mkRes _ []
                                                = l id (res mkRes k) [] t
                                 | (kt,t) <- Map.toList $ ttrieSubs ttrie
                                 , let kt' = updTKey kt
                                       mbm = -- (\v -> tr "XX" (ppTreeTrieMpKey kt >#< (ppTreeTrieMpKey $ updTKey $ replicate (5) (TTM1K [])) >#< ppTreeTrieMpKey kt' >#< ppTreeTrieMpKey k >#< maybe (pp "--") (\f -> ppTreeTrieMpKey $ f $ repeat (TTM1K [])) v) v) $ 
                                             matchTreeTrieMpKeyTo kt' k
                                 , isJust mbm
                                 ]
              
              -- Match with possible wildcard in Key
              TTL_WildInKey -> \updTKey mkRes keys ttrie ->
                case keys of
                  [] -> dflt mkRes ttrie
                  (k : ks)
                     -> (catMaybes mbs ++ concat subs, Nothing)
                     where (subs,mbs)
                             = unzip
                                 [ case ks of
                                     (ksk:ksks)                  -> l id (res mkRes kt) (fromJust m ksk : ksks) t
                                     [] | Map.null (ttrieSubs t) -> l id (res mkRes kt) [] t
                                        | otherwise              -> l id (res mkRes kt) [fromJust m $ repeat (TTM1K [])] t
                                 | (kt,t) <- Map.toList $ ttrieSubs ttrie
                                 , let m = -- (\v -> tr "YY" (ppTreeTrieMpKey k >#< ppTreeTrieMpKey kt >#< maybe (pp "--") (\f -> ppTreeTrieMpKey $ f $ repeat (TTM1K [])) v) v) $ 
                                           matchTreeTrieMpKeyTo k kt
                                 , isJust m
                                 ]
          
          -- Utils
          where dflt mkRes ttrie = ([],fmap (mkRes []) $ ttrieMbVal ttrie)
                res mkRes k = \ks v -> mkRes (k : ks) v

lookupPartialByKey :: (PP k,Ord k) => TreeTrieLookup -> TreeTrieKey k -> TreeTrie k v -> ([v],Maybe v)
lookupPartialByKey = lookupPartialByKey' (\_ v -> v)

lookupByKey, lookup :: (PP k,Ord k) => TreeTrieKey k -> TreeTrie k v -> Maybe v
lookupByKey keys ttrie = snd $ lookupPartialByKey TTL_WildInTrie keys ttrie

lookup = lookupByKey

-- | Convert the lookup result to a list of results
lookupResultToList :: ([v],Maybe v) -> [v]
lookupResultToList (vs,mv) = maybeToList mv ++ vs

-------------------------------------------------------------------------------------------
--- Observation
-------------------------------------------------------------------------------------------

isEmpty :: TreeTrie k v -> Bool
isEmpty ttrie
  =  isNothing (ttrieMbVal ttrie)
  && Map.null  (ttrieSubs ttrie)

null :: TreeTrie k v -> Bool
null = isEmpty

elems :: TreeTrie k v -> [v]
elems = map snd . toListByKey

-------------------------------------------------------------------------------------------
--- Construction
-------------------------------------------------------------------------------------------

singleton :: Ord k => TreeTrieKey k -> v -> TreeTrie k v
singleton keys val
  = s keys
  where s []       = TreeTrie (Just val) Map.empty
        s (k : ks) = TreeTrie Nothing (Map.singleton k $ singleton ks val) 

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

insertByKeyWith :: Ord k => (v -> v -> v) -> TreeTrieKey k -> v -> TreeTrie k v -> TreeTrie k v
insertByKeyWith cmb keys val ttrie = unionsWith cmb [singleton keys val,ttrie]

insertByKey :: Ord k => TreeTrieKey k -> v -> TreeTrie k v -> TreeTrie k v
insertByKey = insertByKeyWith const

insert :: Ord k => TreeTrieKey k -> v -> TreeTrie k v -> TreeTrie k v
insert = insertByKey

insertKeyable :: (Ord (TrTrKey v),TreeTrieKeyable v) => v -> TreeTrie (TrTrKey v) v -> TreeTrie (TrTrKey v) v
insertKeyable val = insertByKey (toTreeTrieKey val) val

-------------------------------------------------------------------------------------------
--- Delete, ...
-------------------------------------------------------------------------------------------

deleteByKey, delete :: Ord k => TreeTrieKey k -> TreeTrie k v -> TreeTrie k v
deleteByKey keys ttrie
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

-------------------------------------------------------------------------------------------
--- Instances: Serialize
-------------------------------------------------------------------------------------------

instance Serialize k => Serialize (TreeTrie1Key k) where
  sput (TT1K_Any            ) = sputWord8 0
  sput (TT1K_One   a        ) = sputWord8 1 >> sput a
  sget
    = do t <- sgetWord8
         case t of
            0 -> return TT1K_Any
            1 -> liftM  TT1K_One         sget

instance Serialize k => Serialize (TreeTrieMp1Key k) where
  sput (TTM1K_Any            ) = sputWord8 0 -- >> sput a
  sput (TTM1K       a        ) = sputWord8 1 >> sput a
  sget
    = do t <- sgetWord8
         case t of
            0 -> return TTM1K_Any     -- sget
            1 -> liftM  TTM1K         sget

instance (Ord k, Serialize k, Serialize v) => Serialize (TreeTrie k v) where
  sput (TreeTrie a b) = sput a >> sput b
  sget = liftM2 TreeTrie sget sget

-------------------------------------------------------------------------------------------
--- Test
-------------------------------------------------------------------------------------------

{-
test1
  = fromListByKey
      [ ( [ [TTM1K [TT1K_One "C"]]
          , [TTM1K [TT1K_Any, TT1K_One "P"]]
          , [TTM1K [TT1K_One "D", TT1K_One "F"], TTM1K []]
          ]
        , "C (* D F) P"
        )
      , ( [ [TTM1K [TT1K_One "C"]]
          , [TTM1K [TT1K_One "B", TT1K_One "P"]]
          , [TTM1K [TT1K_One "D", TT1K_One "F"], TTM1K []]
          ]
        , "C (B D F) P"
        )
      , ( [ [TTM1K [TT1K_One "C"]]
          , [TTM1K [TT1K_One "B", TT1K_One "P"]]
          , [TTM1K [], TTM1K [TT1K_One "Q", TT1K_One "R"]]
          ]
        , "C B (P Q R)"
        )
      , ( [ [TTM1K [TT1K_One "C"]]
          , [TTM1K [TT1K_One "B", TT1K_Any]]
          ]
        , "C B *"
        )
      ]

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
