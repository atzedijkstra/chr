{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, UndecidableInstances, NoMonomorphismRestriction, MultiParamTypeClasses #-}

-------------------------------------------------------------------------------------------
--- CHR solver
-------------------------------------------------------------------------------------------

{-|
Derived from work by Gerrit vd Geest, but greatly adapted to use more efficient searching.

Assumptions (to be documented further)
- The key [Trie.TrieKey Key] used to lookup a constraint in a CHR should be distinguishing enough to be used for the prevention
  of the application of a propagation rule for a 2nd time.

This is a monomorphic Solver, i.e. the solver is polymorph but therefore can only work on 1 type of constraints, rules, etc.
-}

module UHC.Util.CHR.Solve.TreeTrie.Mono
  ( CHRStore
  , emptyCHRStore
  
  , StoredCHR(..)
  
  , chrStoreFromElems
  , chrStoreUnion
  , chrStoreUnions
  , chrStoreSingletonElem
  , chrStoreToList
  , chrStoreElems
  
  , ppCHRStore
  , ppCHRStore'
  
  , SolveStep'(..)
  , SolveStep
  , SolveTrace
  , ppSolveTrace
  
  , SolveState
  , emptySolveState
  , solveStateResetDone
  , chrSolveStateDoneConstraints
  , chrSolveStateTrace
  
  , IsCHRSolvable(..)
  , chrSolve'
  , chrSolve''
  , chrSolveM
  )
  where

import           UHC.Util.CHR.Base
import           UHC.Util.CHR.Key
import           UHC.Util.CHR.Solve.TreeTrie.Internal
import           UHC.Util.Substitutable
import           UHC.Util.VarLookup
import           UHC.Util.VarMp
import           UHC.Util.AssocL
import           UHC.Util.TreeTrie as TreeTrie
import qualified Data.Set as Set
import qualified Data.Map as Map
import           Data.List as List
import           Data.Typeable
import           Data.Data
import           Data.Maybe
import           UHC.Util.Pretty as Pretty
import           UHC.Util.Serialize
import           Control.Monad
import           Control.Monad.State.Strict
import           UHC.Util.Utils

-------------------------------------------------------------------------------------------
--- CHR store, with fast search
-------------------------------------------------------------------------------------------

-- | A CHR as stored in a CHRStore, requiring additional info for efficiency
data StoredCHR c g
  = StoredCHR
      { storedChr       :: !(Rule c g () ())      -- the Rule
      , storedKeyedInx  :: !Int                             -- index of constraint for which is keyed into store
      , storedKeys      :: ![Maybe (CHRKey c)]                  -- keys of all constraints; at storedKeyedInx: Nothing
      , storedIdent     :: !(UsedByKey c)                       -- the identification of a CHR, used for propagation rules (see remark at begin)
      }
  deriving (Typeable)

type instance TTKey (StoredCHR c g) = TTKey c

instance (TTKeyable (Rule c g () ())) => TTKeyable (StoredCHR c g) where
  toTTKey' o schr = toTTKey' o $ storedChr schr

-- | The size of the simplification part of a CHR
storedSimpSz :: StoredCHR c g -> Int
storedSimpSz = ruleSimpSz . storedChr
{-# INLINE storedSimpSz #-}

-- | A CHR store is a trie structure
newtype CHRStore cnstr guard
  = CHRStore
      { chrstoreTrie    :: CHRTrie [StoredCHR cnstr guard]
      }
  deriving (Typeable)

mkCHRStore trie = CHRStore trie

emptyCHRStore :: CHRStore cnstr guard
emptyCHRStore = mkCHRStore emptyCHRTrie

-- | Combine lists of stored CHRs by concat, adapting their identification nr to be unique
cmbStoredCHRs :: [StoredCHR c g] -> [StoredCHR c g] -> [StoredCHR c g]
cmbStoredCHRs s1 s2
  = map (\s@(StoredCHR {storedIdent=(k,nr)}) -> s {storedIdent = (k,nr+l)}) s1 ++ s2
  where l = length s2

instance Show (StoredCHR c g) where
  show _ = "StoredCHR"

ppStoredCHR :: (PP (TTKey c), PP c, PP g) => StoredCHR c g -> PP_Doc
ppStoredCHR c@(StoredCHR {storedIdent=(idKey,idSeqNr)})
  = storedChr c
    >-< indent 2
          (ppParensCommas
            [ pp $ storedKeyedInx c
            , pp $ storedSimpSz c
            , "keys" >#< (ppBracketsCommas $ map (maybe (pp "?") ppTreeTrieKey) $ storedKeys c)
            , "ident" >#< ppParensCommas [ppTreeTrieKey idKey,pp idSeqNr]
            ])

instance (PP (TTKey c), PP c, PP g) => PP (StoredCHR c g) where
  pp = ppStoredCHR

-- | Convert from list to store
chrStoreFromElems :: (TTKeyable c, Ord (TTKey c), TTKey c ~ TrTrKey c) => [Rule c g () ()] -> CHRStore c g
chrStoreFromElems chrs
  = mkCHRStore
    $ chrTrieFromListByKeyWith cmbStoredCHRs
        [ (k,[StoredCHR chr i ks' (concat ks,0)])
        | chr <- chrs
        , let cs = ruleHead chr
              simpSz = ruleSimpSz chr
              ks = map chrToKey cs
        , (c,k,i) <- zip3 cs ks [0..]
        , let (ks1,(_:ks2)) = splitAt i ks
              ks' = map Just ks1 ++ [Nothing] ++ map Just ks2
        ]

chrStoreSingletonElem :: (TTKeyable c, Ord (TTKey c), TTKey c ~ TrTrKey c) => Rule c g () () -> CHRStore c g
chrStoreSingletonElem x = chrStoreFromElems [x]

chrStoreUnion :: (Ord (TTKey c)) => CHRStore c g -> CHRStore c g -> CHRStore c g
chrStoreUnion cs1 cs2 = mkCHRStore $ chrTrieUnionWith cmbStoredCHRs (chrstoreTrie cs1) (chrstoreTrie cs2)
{-# INLINE chrStoreUnion #-}

chrStoreUnions :: (Ord (TTKey c)) => [CHRStore c g] -> CHRStore c g
chrStoreUnions []  = emptyCHRStore
chrStoreUnions [s] = s
chrStoreUnions ss  = foldr1 chrStoreUnion ss
{-# INLINE chrStoreUnions #-}

chrStoreToList :: (Ord (TTKey c)) => CHRStore c g -> [(CHRKey c,[Rule c g () ()])]
chrStoreToList cs
  = [ (k,chrs)
    | (k,e) <- chrTrieToListByKey $ chrstoreTrie cs
    , let chrs = [chr | (StoredCHR {storedChr = chr, storedKeyedInx = 0}) <- e]
    , not $ Prelude.null chrs
    ]

chrStoreElems :: (Ord (TTKey c)) => CHRStore c g -> [Rule c g () ()]
chrStoreElems = concatMap snd . chrStoreToList

ppCHRStore :: (PP c, PP g, Ord (TTKey c), PP (TTKey c)) => CHRStore c g -> PP_Doc
ppCHRStore = ppCurlysCommasBlock . map (\(k,v) -> ppTreeTrieKey k >-< indent 2 (":" >#< ppBracketsCommasBlock v)) . chrStoreToList

ppCHRStore' :: (PP c, PP g, Ord (TTKey c), PP (TTKey c)) => CHRStore c g -> PP_Doc
ppCHRStore' = ppCurlysCommasBlock . map (\(k,v) -> ppTreeTrieKey k >-< indent 2 (":" >#< ppBracketsCommasBlock v)) . chrTrieToListByKey . chrstoreTrie

-------------------------------------------------------------------------------------------
--- Solver trace
-------------------------------------------------------------------------------------------

type SolveStep  c g s = SolveStep'  c (Rule c g () ()) s
type SolveTrace c g s = SolveTrace' c (Rule c g () ()) s

-------------------------------------------------------------------------------------------
--- Cache for maintaining which WorkKey has already had a match
-------------------------------------------------------------------------------------------

-- type SolveMatchCache c g b p s = Map.Map (CHRKey c) [((StoredCHR c g,([WorkKey c],[Work c])),s)]
-- type SolveMatchCache c g b p s = Map.Map (WorkKey c) [((StoredCHR c g,([WorkKey c],[Work c])),s)]
type SolveMatchCache c g b p s = SolveMatchCache' c (StoredCHR c g) s

-------------------------------------------------------------------------------------------
--- Solve state
-------------------------------------------------------------------------------------------

type SolveState c g s = SolveState' c (Rule c g () ()) (StoredCHR c g) s

-------------------------------------------------------------------------------------------
--- Solver
-------------------------------------------------------------------------------------------

-- | (Class alias) API for solving requirements
class ( IsCHRConstraint env c s
      , IsCHRGuard env g s
      , LookupApply s s
      -- , VarUpdatable s s
      , CHREmptySubstitution s
      , TrTrKey c ~ TTKey c
      ) => IsCHRSolvable env c g s
        |  c g -> s

{-
chrSolve
  :: forall env c g s .
     ( IsCHRSolvable env c g s
     )
     => env
     -> CHRStore c g
     -> [c]
     -> [c]
chrSolve env chrStore cnstrs
  = work ++ done
  where (work, done, _ :: SolveTrace c g s) = chrSolve' env chrStore cnstrs
-}

-- | Solve
chrSolve'
  :: forall env c g s .
     ( IsCHRSolvable env c g s
     )
     => [CHRTrOpt]
     -> env
     -> CHRStore c g
     -> [c]
     -> ([c],[c],SolveTrace c g s)
chrSolve' tropts env chrStore cnstrs
  = (wlToList (stWorkList finalState), stDoneCnstrs finalState, stTrace finalState)
  where finalState = chrSolve'' tropts env chrStore cnstrs emptySolveState

-- | Solve
chrSolve''
  :: forall env c g s .
     ( IsCHRSolvable env c g s
     )
     => [CHRTrOpt]
     -> env
     -> CHRStore c g
     -> [c]
     -> SolveState c g s
     -> SolveState c g s
chrSolve'' tropts env chrStore cnstrs prevState
  = flip execState prevState $ chrSolveM tropts env chrStore cnstrs

-- | Solve
chrSolveM
  :: forall env c g s .
     ( IsCHRSolvable env c g s
     )
     => [CHRTrOpt]
     -> env
     -> CHRStore c g
     -> [c]
     -> State (SolveState c g s) ()
chrSolveM tropts env chrStore cnstrs = do
    modify initState
    iter
{-
    modify $
            addStats Map.empty
                [ ("workMatches",ppAssocLV [(ppTreeTrieKey k,pp (fromJust l))
                | (k,c) <- Map.toList $ stCountCnstr st, let l = Map.lookup "workMatched" c, isJust l])
                ]
-}
    modify $ \st -> st {stMatchCache = Map.empty}
  where iter = do
          st <- get
          case st of
            (SolveState {stWorkList = wl@(WorkList {wlQueue = (workHd@(workHdKey,_) : workTl)})}) ->
                case matches of
                  (_:_) -> do
                      put 
{-   
                          $ addStats Map.empty
                                [ ("(0) yes work", ppTreeTrieKey workHdKey)
                                ]
                          $
-}    
                          stmatch
                      expandMatch matches
                    where -- expandMatch :: SolveState c g s -> [((StoredCHR c g, ([WorkKey c], [Work c])), s)] -> SolveState c g s
                          expandMatch ( ( ( schr@(StoredCHR {storedIdent = chrId, storedChr = chr@(Rule {ruleSimpSz = simpSz})})
                                          , (keys,works)
                                          )
                                        , subst
                                        ) : tlMatch
                                      ) = do
                              let b = ruleBody chr
                              st@(SolveState {stWorkList = wl, stHistoryCount = histCount, stUsedRules = usedRules }) <- get
                              let (tlMatchY,tlMatchN) = partition (\(r@(_,(ks,_)),_) -> not (any (`elem` keysSimp) ks || slvIsUsedByPropPart (wlUsedIn wl') r)) tlMatch
                                  (keysSimp,keysProp) = splitAt simpSz keys
                                  usedIn              = Map.singleton (Set.fromList keysProp) (Set.singleton chrId)
                                  (bTodo,bDone)       = splitDone $ map (varUpd subst) b
                                  bTodo'              = wlCnstrToIns wl bTodo
                                  wl' = wlDeleteByKeyAndInsert' histCount keysSimp bTodo'
                                        $ wl { wlUsedIn  = usedIn `wlUsedInUnion` wlUsedIn wl
                                             , wlScanned = []
                                             , wlQueue   = wlQueue wl ++ wlScanned wl
                                             }
                                  st' = st { stWorkList       = wl'
{-  
                                           , stTrace          = SolveStep chr' subst (assocLElts bTodo') bDone : {- SolveDbg (ppwork >-< ppdbg) : -} stTrace st
-}    
                                           , stDoneCnstrSet   = Set.unions [Set.fromList bDone, Set.fromList $ map workCnstr $ take simpSz works, stDoneCnstrSet st]
                                           , stMatchCache     = if List.null bTodo' then stMatchCache st else Map.empty
                                           , stHistoryCount   = histCount + 1
                                           , stUsedRules      = (chr : usedRules)
                                           }
{-   
                                  chr'= subst `varUpd` chr
                                  ppwork = "workkey" >#< ppTreeTrieKey workHdKey >#< ":" >#< (ppBracketsCommas (map (ppTreeTrieKey . fst) workTl) >-< ppBracketsCommas (map (ppTreeTrieKey . fst) $ wlScanned wl))
                                             >-< "workkeys" >#< ppBracketsCommas (map ppTreeTrieKey keys)
                                             >-< "worktrie" >#< wlTrie wl
                                             >-< "schr" >#< schr
                                             >-< "usedin" >#< (ppBracketsCommasBlock $ map (\(k,s) -> ppKs k >#< ppBracketsCommas (map ppUsedByKey $ Set.toList s)) $ Map.toList $ wlUsedIn wl)
                                             >-< "usedin'" >#< (ppBracketsCommasBlock $ map (\(k,s) -> ppKs k >#< ppBracketsCommas (map ppUsedByKey $ Set.toList s)) $ Map.toList $ wlUsedIn wl')
                                         where ppKs ks = ppBracketsCommas $ map ppTreeTrieKey $ Set.toList ks
-}   
                              put
{-   
                                  $ addStats Map.empty
                                        [ ("chr",pp chr')
                                        , ("leftover sz", pp (length tlMatchY))
                                        , ("filtered out sz", pp (length tlMatchN))
                                        , ("new done sz", pp (length bDone))
                                        , ("new todo sz", pp (length bTodo))
                                        , ("wl queue sz", pp (length (wlQueue wl')))
                                        , ("wl usedin sz", pp (Map.size (wlUsedIn wl')))
                                        , ("done sz", pp (Set.size (stDoneCnstrSet st')))
                                        , ("hist cnt", pp histCount)
                                        ]
                                  $
-}   
                                  st'
                              expandMatch tlMatchY

                          expandMatch _ 
                            = iter
                          
                  _ -> do
                      put
{-   
                          $ addStats Map.empty
                                [ ("no match work", ppTreeTrieKey workHdKey)
                                , ("wl queue sz", pp (length (wlQueue wl')))
                                ]
                          $
-}    
                          st'
                      iter
                    where wl' = wl { wlScanned = workHd : wlScanned wl, wlQueue = workTl }
                          st' = stmatch { stWorkList = wl' {- , stTrace = SolveDbg (ppdbg) : stTrace stmatch -} }
              where (matches,lastQuery {- ,ppdbg,stats -}) = workMatches st
{-  
                    stmatch = addStats stats [("(a) workHd", ppTreeTrieKey workHdKey), ("(b) matches", ppBracketsCommasBlock [ s `varUpd` storedChr schr | ((schr,_),s) <- matches ])]
-}
                    stmatch =  
                                (st { stCountCnstr = scntInc workHdKey "workMatched" $ stCountCnstr st
                                    , stMatchCache = Map.insert workHdKey [] (stMatchCache st)
                                    , stLastQuery  = lastQuery
                                    })
            _ -> do
                return ()

        mkStats  stats new    = stats `Map.union` Map.fromList (assocLMapKey showPP new)
{-
        addStats stats new st = st { stTrace = SolveStats (mkStats stats new) : stTrace st }
-}
        addStats _     _   st = st

        mkDbgPP o | o `elem` tropts = id
                  | otherwise       = const Pretty.empty

        workMatches st@(SolveState {stWorkList = WorkList {wlQueue = (workHd@(workHdKey,Work {workTime = workHdTm}) : _), wlTrie = wlTrie, wlUsedIn = wlUsedIn}, stHistoryCount = histCount, stLastQuery = lastQuery})
          | isJust mbInCache  = ( fromJust mbInCache
                                , lastQuery
                                {-
                                , Pretty.empty
                                , mkStats Map.empty [("cache sz",pp (Map.size (stMatchCache st)))]
                                -}
                                )
          | otherwise         = ( r5
                                , foldr lqUnion lastQuery [ lqSingleton ck wks histCount | (_,(_,(ck,wks))) <- r23 ]
                                -- , Pretty.empty
                                -- , mkDbgPP CHRTrOpt_Lookup $ pp2 >-< pp2b >-< {- pp2c >-< -} pp3
{-
                                , mkStats Map.empty [("(1) lookup sz",pp (length r2)), ("(2) cand sz",pp (length r3)), ("(3) unused cand sz",pp (length r4)), ("(4) final cand sz",pp (length r5))]
-}
{-
                                , Pretty.empty
-}
                                -- , Map.empty
                                )
          where -- cache result, if present use that, otherwise the below computation
                mbInCache = Map.lookup workHdKey (stMatchCache st)
                
                -- results, stepwise computed for later reference in debugging output
                -- basic search result
                r2 :: [StoredCHR c g]                                       -- CHRs matching workHdKey
                r2  = concat                                                    -- flatten
                        $ TreeTrie.lookupResultToList                                   -- convert to list
                        $ chrTrieLookup chrLookupHowWildAtTrie workHdKey        -- lookup the store, allowing too many results
                        $ chrstoreTrie chrStore
                
                -- lookup further info in wlTrie, in particular to find out what has been done already
                r23 :: [( StoredCHR c g                                     -- the CHR
                        , ( [( [(CHRKey c, Work c)]                             -- for each CHR the list of constraints, all possible work matches
                             , [(CHRKey c, Work c)]
                             )]
                          , (CHRKey c, Set.Set (CHRKey c))
                        ) )]
                r23 = map (\c -> (c, slvCandidate workHdKey lastQuery wlTrie c)) r2
                
                -- possible matches
                r3, r4
                    :: [( StoredCHR c g                                     -- the matched CHR
                        , ( [CHRKey c]                                            -- possible matching constraints (matching with the CHR constraints), as Keys, as Works
                          , [Work c]
                        ) )]
                r3  = concatMap (\(c,cands) -> zip (repeat c) (map unzip $ slvCombine cands)) $ r23
                
                -- same, but now restricted to not used earlier as indicated by the worklist
                r4  = filter (not . slvIsUsedByPropPart wlUsedIn) r3
                
                -- finally, the 'real' match of the 'real' constraint, yielding (by tupling) substitutions instantiating the found trie matches
                r5  :: [( ( StoredCHR c g
                          , ( [CHRKey c]          
                            , [Work c]
                          ) )
                        , s
                        )]
                r5  = mapMaybe (\r@(chr,kw@(_,works)) -> fmap (\s -> (r,s)) $ slvMatch env chr (map workCnstr works)) r4

                -- debug info
                pp2  = "lookups"    >#< ("for" >#< ppTreeTrieKey workHdKey >-< ppBracketsCommasBlock r2)
                pp2b = "cand1"      >#< ("lastQ" >#< ppLastQuery lastQuery >-< vlist [ pp (storedKeyedInx chr) | (chr,mtch) <- r23 ])
                -- pp2b = "cand1"      >#< (ppBracketsCommasBlock $ map (ppBracketsCommasBlock . map (ppBracketsCommasBlock . map (\(k,w) -> ppTreeTrieKey k >#< w)) . fst . candidate) r2)
                -- pp2c = "cand2"      >#< (ppBracketsCommasBlock $ map (ppBracketsCommasBlock . map (ppBracketsCommasBlock) . combineToDistinguishedElts . fst . candidate) r2)
                pp3  = "candidates" >#< (ppBracketsCommasBlock $ map (\(chr,(ks,ws)) -> "chr" >#< chr >-< "keys" >#< ppBracketsCommas (map ppTreeTrieKey ks) >-< "works" >#< ppBracketsCommasBlock ws) $ r3)
{-
-}
        initState st = st { stWorkList = wlInsert (stHistoryCount st) wlnew $ stWorkList st, stDoneCnstrSet = Set.unions [Set.fromList done, stDoneCnstrSet st] }
                     where (wlnew,done) = splitDone cnstrs
        splitDone  = partition cnstrRequiresSolve

-- | Extract candidates matching a CHRKey.
--   Return a list of CHR matches,
--     each match expressed as the list of constraints (in the form of Work + Key) found in the workList wlTrie, thus giving all combis with constraints as part of a CHR,
--     partititioned on before or after last query time (to avoid work duplication later)
slvCandidate
  :: (Ord (TTKey c), PP (TTKey c))
     => CHRKey c
     -> LastQuery c
     -> WorkTrie c
     -> StoredCHR c g
     -> ( [( [(CHRKey c, Work c)]
           , [(CHRKey c, Work c)]
           )]
        , (CHRKey c, Set.Set (CHRKey c))
        )
slvCandidate workHdKey lastQuery wlTrie (StoredCHR {storedIdent = (ck,_), storedKeys = ks, storedChr = chr})
  = ( map (maybe (lkup chrLookupHowExact workHdKey) (lkup chrLookupHowWildAtKey)) ks
    , ( ck
      , Set.fromList $ map (maybe workHdKey id) ks
    ) )
  where lkup how k = partition (\(_,w) -> workTime w < lastQueryTm)
                       $ map (\w -> (workKey w,w))
                       $ TreeTrie.lookupResultToList
                       $ chrTrieLookup how k wlTrie
                   where lastQueryTm = lqLookupW k $ lqLookupC ck lastQuery
{-# INLINE slvCandidate #-}

-- | Check whether the CHR propagation part of a match already has been used (i.e. propagated) earlier,
--   this to avoid duplicate propagation.
slvIsUsedByPropPart
  :: (Ord k, Ord (TTKey c))
     => Map.Map (Set.Set k) (Set.Set (UsedByKey c))
     -> (StoredCHR c g, ([k], t))
     -> Bool
slvIsUsedByPropPart wlUsedIn (chr,(keys,_))
  = fnd $ drop (storedSimpSz chr) keys
  where fnd k = maybe False (storedIdent chr `Set.member`) $ Map.lookup (Set.fromList k) wlUsedIn
{-# INLINE slvIsUsedByPropPart #-}

-- | Match the stored CHR with a set of possible constraints, giving a substitution on success
slvMatch
  :: ( CHREmptySubstitution s
     , CHRMatchable env c s
     , CHRCheckable env g s
     , LookupApply s s
     )
     => env -> StoredCHR c g -> [c] -> Maybe s
slvMatch env chr cnstrs
  = foldl cmb (Just chrEmptySubst) $ matches chr cnstrs ++ checks chr
  where matches (StoredCHR {storedChr = Rule {ruleHead = hc}}) cnstrs
          = zipWith mt hc cnstrs
          where mt cFr cTo subst = chrMatchTo env subst cFr cTo
        checks (StoredCHR {storedChr = Rule {ruleGuard = gd}})
          = map chk gd
          where chk g subst = chrCheck env subst g
        cmb (Just s) next = fmap (|+> s) $ next s
        cmb _        _    = Nothing
{-# INLINE slvMatch #-}

-------------------------------------------------------------------------------------------
--- Instances: Serialize
-------------------------------------------------------------------------------------------

instance (Ord (TTKey c), Serialize (TTKey c), Serialize c, Serialize g) => Serialize (CHRStore c g) where
  sput (CHRStore a) = sput a
  sget = liftM CHRStore sget
  
instance (Serialize c, Serialize g, Serialize (TTKey c)) => Serialize (StoredCHR c g) where
  sput (StoredCHR a b c d) = sput a >> sput b >> sput c >> sput d
  sget = liftM4 StoredCHR sget sget sget sget

