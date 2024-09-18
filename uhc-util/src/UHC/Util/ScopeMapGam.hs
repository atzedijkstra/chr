{- |
Environment/Gamma where the lexical level + scoping is used to provide nesting behavior.
Both a SGam and its entries know at which scope they are.

Insertion is efficient, lookup also, because a single Map is used.

The Map holds multiple entries, each with its own scope identifier.
An SGam holds
- a stack of scopes, encoding the nesting, where
- each scope holds mappings for MetaLev's

Results are filtered out w.r.t. this stack, i.e. are checked to be in scope.
In principle this can be done eagerly, that is, immediately after a change in scope, in particular in sgamPop.
After some experimentation it did turn out that doing this lazily is overall faster, that is, when the SGam is consulted (lookup, conversion to association list, etc).
Conceptually thus the invariant is that no entry is in the map which is not in scope. Guaranteeing this invariant is thus not done by the one function breaking it (sgamPop).

-}

{-# LANGUAGE DeriveDataTypeable #-}

module UHC.Util.ScopeMapGam
    ( SGam
    , emptySGam

    -- * Folding
    , sgamFilterMapEltAccumWithKey, sgamMapEltWithKey, sgamMapThr, sgamMap

    -- * Construction & Destruction
    , sgamPop, sgamTop
    , sgamPushNew, sgamPushGam
    , sgamMetaLevSingleton, sgamSingleton
    , sgamUnionWith, sgamUnion
    , sgamPartitionEltWithKey, sgamPartitionWithKey
    , sgamUnzip
    
    -- * Deletion
    -- , sgamDeleteDupOnTop
    
    -- * Update
    , sgamAlterDupOnTop
    
    -- * Lookup
    , sgamLookupMetaLevDup

    -- * Conversion
    , sgamToAssocDupL, sgamFromAssocDupL
    , sgamNoDups

    -- * Re-exports
    , MetaLev
    , metaLevVal
    )
  where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe
import Data.List
import UHC.Util.VarMp
import UHC.Util.Utils
import UHC.Util.AssocL
-- import EH100.Base.Common
import Data.Typeable (Typeable)
-- import Data.Generics (Data)
import UHC.Util.Serialize
import Control.Monad
-- import EH100.Base.Binary

-- Scope Gam, a Gam with entries having a level in a scope, and the Gam a scope

type Scp = [Int]                                    -- ^ a stack of scope idents defines what's in scope

data SGamElt v
  = SGamElt
      { sgeScpId    :: !Int                         -- ^ scope ident
      , sgeVal      :: v                            -- ^ the value
      }
  deriving (Typeable, Generic)

type SMap k v = VarMp' k [SGamElt v]

emptySMap :: SMap k v
emptySMap = emptyVarMp

data SGam k v
  = SGam
      { sgScpId     :: !Int                         -- ^ current scope, increment with each change in scope
      , sgScp       :: !Scp                         -- ^ scope stack
      , sgMap       :: SMap k v                     -- ^ map holding the values
      }
  deriving (Typeable, Generic)

mkSGam :: SMap k v -> SGam k v
mkSGam = SGam 0 [0]

emptySGam :: SGam k v
emptySGam = mkSGam emptySMap

instance Show (SGam k v) where
  show _ = "SGam"


-- | scope ident in scope?
inScp :: Scp -> Int -> Bool
inScp = flip elem
{-# INLINE inScp #-}

-- | sgam elt in scope?
sgameltInScp :: Scp -> SGamElt v -> Bool
sgameltInScp scp = inScp scp . sgeScpId
{-# INLINE sgameltInScp #-}

-- | partition the in scopes
sgameltPartitionInScp :: Scp -> [SGamElt v] -> ([SGamElt v], [SGamElt v], [v'] -> [v'] -> [v'])
sgameltPartitionInScp scp = partitionAndRebuild (sgameltInScp scp)
{-# INLINE sgameltPartitionInScp #-}

-- | filter the in scopes
sgameltFilterInScp :: Scp -> [SGamElt v] -> [SGamElt v]
sgameltFilterInScp scp = filter (sgameltInScp scp)
{-# INLINE sgameltFilterInScp #-}

-- | map the in scopes
sgameltMapInScp :: Scp -> (v -> v) -> [SGamElt v] -> [SGamElt v]
sgameltMapInScp scp f = map (\e -> if sgameltInScp scp e then e {sgeVal = f (sgeVal e)} else e)
{-# INLINE sgameltMapInScp #-}

-- | extract the in scopes
sgameltGetFilterInScp :: Scp -> (v -> v') -> [SGamElt v] -> [v']
sgameltGetFilterInScp scp f es = [ f (sgeVal e) | e <- es, sgameltInScp scp e ]
{-# INLINE sgameltGetFilterInScp #-}

-- | filter out the out of scopes, applying a mapping function on the fly
mapFilterInScp' :: Ord k => Scp -> ([SGamElt v] -> [SGamElt v]) -> SMap k v -> SMap k v
mapFilterInScp' scp f m
  = varmpMapMaybe (\es -> maybeNull Nothing (Just . f) $ sgameltFilterInScp scp es) m
{-# INLINE mapFilterInScp' #-}

mapFilterInScp :: Ord k => Scp -> (SGamElt v -> SGamElt v) -> SMap k v -> SMap k v
mapFilterInScp scp f m
  = mapFilterInScp' scp (map f) m
{-# INLINE mapFilterInScp #-}

sgamFilterInScp :: Ord k => SGam k v -> SGam k v
sgamFilterInScp g@(SGam {sgScp = scp, sgMap = m})
  = g {sgMap = mapFilterInScp scp id m}
{-# INLINE sgamFilterInScp #-}

-- | do it all: map, filter, fold
sgamFilterMapEltAccumWithKey
  :: (Ord k')
       => (k -> SGamElt v -> Bool)
          -> (k -> SGamElt v -> acc -> (k',SGamElt v',acc))
          -> (k -> SGamElt v -> acc -> acc)
          -> acc -> SGam k v -> (SGam k' v',acc)
sgamFilterMapEltAccumWithKey p fyes fno a g
  = (g {sgMap = mkVarMp m'},a')
  where (m,_)   = varmpAsMap (sgMap g)
        (m',a') = Map.foldrWithKey
                    (\k es ma@(m,a)
                      -> foldr (\e (m,a)
                                 -> if p k e
                                    then let (k',e',a') = fyes k e a
                                         in  (Map.insertWith (++) k' [e'] m,a')
                                    else (m,fno k e a)
                               ) ma
                         $ sgameltFilterInScp (sgScp g) es
                    ) (Map.empty,a) m

sgamMapEltWithKey :: (Ord k,Ord k') => (k -> SGamElt v -> (k',SGamElt v')) -> SGam k v -> SGam k' v'
sgamMapEltWithKey f g
  = g'
  where (g',_) = sgamFilterMapEltAccumWithKey (\_ _ -> True) (\k e a -> let (k',e') = f k e in (k',e',a)) undefined () g

sgamMapThr :: (Ord k,Ord k') => ((k,v) -> t -> ((k',v'),t)) -> t -> SGam k v -> (SGam k' v',t)
sgamMapThr f thr g = sgamFilterMapEltAccumWithKey (\_ _ -> True) (\k e thr -> let ((k',v'),thr') = f (k,sgeVal e) thr in (k',e {sgeVal = v'},thr')) undefined thr g

sgamMap :: (Ord k,Ord k') => ((k,v) -> (k',v')) -> SGam k v -> SGam k' v'
sgamMap f g = sgamMapEltWithKey (\k e -> let (k',v') = f (k,sgeVal e) in (k',e {sgeVal = v'})) g

-- | Construct singleton gam, on a particular meta level
sgamMetaLevSingleton :: Ord k => MetaLev -> k -> v -> SGam k v
sgamMetaLevSingleton mlev k v = mkSGam (varlookupSingletonWithMetaLev mlev k [SGamElt 0 v])

-- | Construct singleton gam
sgamSingleton :: Ord k => k -> v -> SGam k v
sgamSingleton = sgamMetaLevSingleton metaLevVal

-- | combine gam, g1 is added to g2 with scope of g2
sgamUnionWith :: Ord k => Maybe (v -> [v] -> [v]) -> SGam k v -> SGam k v -> SGam k v
sgamUnionWith cmb g1@(SGam {sgScp = scp1, sgMap = m1}) g2@(SGam {sgScp = scp2@(hscp2:_), sgMap = m2})
  = g2 {sgMap = varmpUnionWith cmb' m1' m2}
  where m1' = mapFilterInScp scp1 (\e -> e {sgeScpId = hscp2}) m1
        cmb' = maybe (++)
                     (\c -> \l1 l2 -> concat
                        [ map (SGamElt scp) $ foldr c [] $ map sgeVal g
                        | g@(SGamElt {sgeScpId = scp} : _) <- groupSortOn sgeScpId $ l1 ++ l2
                        ]
                     )
                     cmb

-- combine gam, g1 is added to g2 with scope of g2
sgamUnion :: Ord k => SGam k v -> SGam k v -> SGam k v
sgamUnion = sgamUnionWith Nothing
{-# INLINE sgamUnion #-}

-- | equivalent of partition
sgamPartitionEltWithKey :: Ord k => (k -> SGamElt v -> Bool) -> SGam k v -> (SGam k v,SGam k v)
sgamPartitionEltWithKey p g
  = (g1, SGam (sgScpId g1) (sgScp g1) m2)
  where (g1,m2) = sgamFilterMapEltAccumWithKey p (\k e a -> (k,e,a)) (\k e a -> varmpInsertWith (++) k [e] a) emptySMap g

sgamPartitionWithKey :: Ord k => (k -> v -> Bool) -> SGam k v -> (SGam k v,SGam k v)
sgamPartitionWithKey p = sgamPartitionEltWithKey (\k e -> p k (sgeVal e))

-- | equivalent of unzip
sgamUnzip :: Ord k => SGam k (v1,v2) -> (SGam k v1,SGam k v2)
sgamUnzip g
  = (g1, g1 {sgMap = m2})
  where (g1,m2) = sgamFilterMapEltAccumWithKey (\_ _ -> True) (\k e@(SGamElt {sgeVal = (v1,v2)}) m -> (k,e {sgeVal = v1},varmpInsertWith (++) k [e {sgeVal = v2}] m)) undefined emptySMap g

-- | split gam in top and the rest, both with the same scope
sgamPop :: Ord k => SGam k v -> (SGam k v, SGam k v)
sgamPop g@(SGam {sgMap = m, sgScpId = scpId, sgScp = scp@(hscp:tscp)})
  = (SGam scpId [hscp] m, SGam scpId tscp m)
  -- = (sgamFilterInScp $ SGam scpId [hscp] m, sgamFilterInScp $ SGam scpId tscp m)

-- | top gam, with same scope as g
sgamTop :: Ord k => SGam k v -> SGam k v
sgamTop g
  = fst $ sgamPop g

-- | enter a new scope
sgamPushNew :: SGam k v -> SGam k v
sgamPushNew g
 = g {sgScpId = si, sgScp = si : sgScp g}
 where si = sgScpId g + 1

-- | enter a new scope, add g1 in that scope to g2
sgamPushGam :: Ord k => SGam k v -> SGam k v -> SGam k v
sgamPushGam g1 g2 = g1 `sgamUnion` sgamPushNew g2

{- unfinished...
-- | delete an in scope entry, only if on top, using a function splitting the list of values into those which are removal candidates and not
sgamDeleteDupOnTop :: Ord k => ([SGamElt v] -> ([SGamElt v],[SGamElt v])) -> k -> SGam k v -> SGam k v
sgamDeleteDupOnTop split k g@(SGam {sgMap = m, sgScp = scp@(hscp:_)})
  = g {sgMap = update updDel k m}
  where updDel vs = if null all then Nothing else Just all
          where (del,leave) = split $ sgameltFilterInScp scp vs
                del' = filter (\v -> sgeScpId v == hscp) del
                all = del' ++ leave
-}

-- | Alter on top of the scope stack, including all duplicates
sgamAlterDupOnTop :: Ord k => (Maybe v -> Maybe v) -> k -> SGam k v -> SGam k v
sgamAlterDupOnTop f k g@(SGam {sgMap = m, sgScp = scp@(hscp:_)})
  = g {sgMap = varmpAlter alt k m}
  where alt Nothing   = fmap (\v -> [SGamElt hscp v]) $ f Nothing
        alt (Just vs) = if null vs' then Nothing else Just vs'
          where (inscp,leave,mk) = sgameltPartitionInScp scp vs
                vs' = catMaybes $ mk (map (\e -> fmap (\v -> e {sgeVal = v}) $ f $ Just $ sgeVal e) inscp) (map Just leave)

-- | lookup, return at least one found value, otherwise Nothing
sgamLookupMetaLevDup :: Ord k => MetaLev -> k -> SGam k v -> Maybe [v]
sgamLookupMetaLevDup mlev k g@(SGam {sgMap = m, sgScpId = scpId, sgScp = scp})
  = case varlookupWithMetaLev mlev k m of
      Just es | not (null vs)
        -> Just vs
        where vs = {- map sgeVal es -- -} sgameltGetFilterInScp scp id es
      _ -> Nothing

-- | convert to association list, with all duplicates, scope is lost
sgamToAssocDupL :: Ord k => SGam k v -> AssocL k [v]
sgamToAssocDupL g@(SGam {sgScp = scp, sgMap = m})
  = varmpToAssocL $ varmpMap (map sgeVal) $ sgMap $ sgamFilterInScp g

-- | convert from association list, assume default scope
sgamFromAssocDupL :: Ord k => AssocL k [v] -> SGam k v
sgamFromAssocDupL l
  = mkSGam m
  where m = varmpMap (map (SGamElt 0)) $ assocLToVarMp l

-- | get rid of duplicate entries, by taking the first of them all
sgamNoDups :: Ord k => SGam k v -> SGam k v
sgamNoDups g@(SGam {sgScp = scp, sgMap = m})
  = g {sgMap = mapFilterInScp' scp (\(e:_) -> [e]) m}

instance (Serialize v) => Serialize (SGamElt v) where
  -- sput (SGamElt a b) = sput a >> sput b
  -- sget = liftM2 SGamElt sget sget

instance (Ord k, Serialize k, Serialize v) => Serialize (SGam k v) where
  -- sput (SGam a b c) = sput a >> sput b >> sput c
  -- sget = liftM3 SGam sget sget sget

-- instance (Binary v) => Serialize (SGamElt v)
-- instance (Ord k, Binary k, Binary v) => Serialize (SGam k v)

