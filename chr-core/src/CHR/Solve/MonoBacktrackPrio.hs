{-# LANGUAGE ConstraintKinds, ScopedTypeVariables, StandaloneDeriving, UndecidableInstances, NoMonomorphismRestriction, MultiParamTypeClasses, TemplateHaskell, FunctionalDependencies #-}

-------------------------------------------------------------------------------------------
--- CHR solver
-------------------------------------------------------------------------------------------

{-|
Under development (as of 20160218).

Solver is:
- Monomorphic, i.e. the solver is polymorph but therefore can only work on 1 type of constraints, rules, etc.
- Knows about variables for which substitutions can be found, substitutions are part of found solutions.
- Backtracking (on variable bindings/substitutions), multiple solution alternatives are explored.
- Found rules are applied in an order described by priorities associated with rules. Priorities can be dynamic, i.e. depend on terms in rules.

See

"A Flexible Search Framework for CHR", Leslie De Koninck, Tom Schrijvers, and Bart Demoen.
http://link.springer.com/10.1007/978-3-540-92243-8_2
-}

module CHR.Solve.MonoBacktrackPrio
  ( Verbosity(..)

  , CHRGlobState(..)
  , emptyCHRGlobState
  , chrgstVarToNmMp
  , chrgstStatNrSolveSteps
  
  , CHRBackState(..)
  , emptyCHRBackState
  
  , emptyCHRStore
  
  , CHRMonoBacktrackPrioT
  , MonoBacktrackPrio
  , runCHRMonoBacktrackPrioT
  
  , addRule
  
  , addConstraintAsWork
  
  , SolverResult(..)
  , ppSolverResult
  
  , CHRSolveOpts(..)
  , defaultCHRSolveOpts
  
  , StoredCHR
  , storedChrRule'
  
  , chrSolve
  
  , slvFreshSubst
  
  , getSolveTrace
    
  , IsCHRSolvable(..)
  )
  where

import           CHR.Utils
import           CHR.Data.Lens
import           CHR.Data.Lookup                                (Lookup, LookupApply, Scoped)
import qualified CHR.Data.Lookup                                as Lk
import qualified CHR.Data.TreeTrie                              as TT
import           CHR.Data.VarLookup

import qualified Data.Set                                       as Set
import qualified Data.PQueue.Prio.Min                           as Que
import qualified Data.Map.Strict                                as Map
import qualified Data.HashMap.Strict                            as MapH
import qualified Data.IntMap.Strict                             as IntMap
import qualified Data.IntSet                                    as IntSet
import qualified Data.Sequence                                  as Seq
import           Data.List                                      as List
import           Data.Typeable
import           Data.Maybe

import           Control.Monad
-- import           Control.Monad.IO.Class
import           Control.Monad.Except
import           Control.Monad.State.Strict
import           Control.Monad.LogicState

import           CHR.Pretty                                     as Pretty
import           CHR.Types.Core
import           CHR.Types.Rule
import           CHR.Data.Substitutable
import           CHR.Data.AssocL
import           CHR.Data.Fresh

import           CHR.Types

-------------------------------------------------------------------------------------------
--- Verbosity
-------------------------------------------------------------------------------------------

data Verbosity
  = Verbosity_Quiet         -- default
  | Verbosity_Normal
  | Verbosity_Debug
  | Verbosity_ALot
  deriving (Eq, Ord, Show, Enum, Typeable)

-------------------------------------------------------------------------------------------
--- A CHR as stored
-------------------------------------------------------------------------------------------

-- | Index into table of CHR's, allowing for indirection required for sharing of rules by search for different constraints in the head
type CHRInx = Int

-- | Index into rule and head constraint
data CHRConstraintInx =
  CHRConstraintInx 
    { chrciInx :: {-# UNPACK #-} !CHRInx
    , chrciAt  :: {-# UNPACK #-} !Int
    }
  deriving (Eq, Ord, Show)

instance PP CHRConstraintInx where
  pp (CHRConstraintInx i j) = i >|< "." >|< j

-- | A CHR as stored in a CHRStore, requiring additional info for efficiency
data StoredCHR c g bp p
  = StoredCHR
      { _storedHeadKeys  :: ![CHRKey c]                        -- ^ the keys corresponding to the head of the rule
      , _storedChrRule   :: !(Rule c g bp p)                          -- ^ the rule
      , _storedChrInx    :: {-# UNPACK #-} !CHRInx                                -- ^ index of constraint for which is keyed into store
      }
  deriving (Typeable)
  
storedChrRule' :: StoredCHR c g bp p -> Rule c g bp p
storedChrRule' = _storedChrRule

-- | A CHR store is a trie structure
data CHRStore cnstr guard bprio prio
  = CHRStore
      { _chrstoreTrie    :: TT.TreeTrie (TT.TrTrKey cnstr) [CHRConstraintInx]                       -- ^ map from the search key of a rule to the index into tabl
      , _chrstoreTable   :: IntMap.IntMap (StoredCHR cnstr guard bprio prio)      -- ^ (possibly multiple) rules for a key
      }
  deriving (Typeable)

emptyCHRStore :: TT.TTCtxt (TT.TrTrKey cnstr) => CHRStore cnstr guard bprio prio
emptyCHRStore = CHRStore TT.empty IntMap.empty

-------------------------------------------------------------------------------------------
--- Store holding work, split up in global and backtrackable part
-------------------------------------------------------------------------------------------

type WorkInx = WorkTime

type WorkInxSet = IntSet.IntSet

data WorkStore cnstr
  = WorkStore
      { _wkstoreTrie     :: !(TT.TreeTrie (TT.TrTrKey cnstr) [WorkInx])                -- ^ map from the search key of a constraint to index in table
      , _wkstoreTable    :: !(IntMap.IntMap (Work cnstr))      -- ^ all the work ever entered. FIXME: do GC
      , _wkstoreNextFreeWorkInx       :: {-# UNPACK #-} !WorkTime                                        -- ^ Next free work/constraint identification, used by solving to identify whether a rule has been used for a constraint.
      }
  deriving (Typeable)

emptyWorkStore :: TT.TTCtxt (TT.TrTrKey cnstr) => WorkStore cnstr
emptyWorkStore = WorkStore TT.empty IntMap.empty initWorkTime

data WorkQueue
  = WorkQueue
      { _wkqueueActive          :: !WorkInxSet                  -- ^ active queue, work will be taken off from this one
      , _wkqueueRedo            :: !WorkInxSet                  -- ^ redo queue, holding work which could not immediately be reduced, but later on might be
      , _wkqueueDidSomething    :: !Bool                        -- ^ flag indicating some work was done; if False and active queue is empty we stop solving
      }
  deriving (Typeable)

emptyWorkQueue :: WorkQueue
emptyWorkQueue = WorkQueue IntSet.empty IntSet.empty True

-------------------------------------------------------------------------------------------
--- A matched combi of chr and work
-------------------------------------------------------------------------------------------

-- | Already matched combi of chr and work
data MatchedCombi' c w =
  MatchedCombi
    { mcCHR      :: !c              -- ^ the CHR
    , mcWork     :: ![w]            -- ^ the work matched for this CHR
    }
  deriving (Eq, Ord)

instance Show (MatchedCombi' c w) where
  show _ = "MatchedCombi"

instance (PP c, PP w) => PP (MatchedCombi' c w) where
  pp (MatchedCombi c ws) = ppParensCommas [pp c, ppBracketsCommas ws]

type MatchedCombi = MatchedCombi' CHRInx WorkInx

-------------------------------------------------------------------------------------------
--- Solver reduction step
-------------------------------------------------------------------------------------------

-- | Description of 1 chr reduction step taken by the solver
data SolverReductionStep' c w
  = SolverReductionStep
      { slvredMatchedCombi        :: !(MatchedCombi' c w)
      , slvredChosenBodyAltInx    :: {-# UNPACK #-} !Int
      , slvredNewWork             :: !(Map.Map ConstraintSolvesVia [w])
      }
  | SolverReductionDBG PP_Doc

type SolverReductionStep = SolverReductionStep' CHRInx WorkInx

instance Show (SolverReductionStep' c w) where
  show _ = "SolverReductionStep"

instance {-# OVERLAPPABLE #-} (PP c, PP w) => PP (SolverReductionStep' c w) where
  pp (SolverReductionStep (MatchedCombi ci ws) a wns) = "STEP" >#< ci >|< "." >|< a >-< indent 2 ("+" >#< ppBracketsCommas ws >-< "-> (new)" >#< (ppAssocL $ Map.toList $ Map.map ppBracketsCommas wns)) -- (ppBracketsCommas wns >-< ppBracketsCommas wnbs)
  pp (SolverReductionDBG p) = "DBG" >#< p

instance (PP w) => PP (SolverReductionStep' Int w) where
  pp (SolverReductionStep (MatchedCombi ci ws) a wns) = ci >|< "." >|< a >#< "+" >#< ppBracketsCommas ws >#< "-> (new)" >#< (ppAssocL $ Map.toList $ Map.map ppBracketsCommas wns) -- (ppBracketsCommas wns >-< ppBracketsCommas wnbs)
  pp (SolverReductionDBG p) = "DBG" >#< p

-------------------------------------------------------------------------------------------
--- Waiting (for var resolution) work
-------------------------------------------------------------------------------------------

-- | Admin for waiting work
data WaitForVar s
  = WaitForVar
      { _waitForVarVars      :: !(CHRWaitForVarSet s)
      , _waitForVarWorkInx   :: {-# UNPACK #-} !WorkInx
      }
  deriving (Typeable)

-- | Index into collection of 'WaitForVar'
type WaitInx = Int

-------------------------------------------------------------------------------------------
--- The CHR monad, state, etc. Used to interact with store and solver
-------------------------------------------------------------------------------------------

-- | Global state
data CHRGlobState cnstr guard bprio prio subst env m
  = CHRGlobState
      { _chrgstStore                 :: !(CHRStore cnstr guard bprio prio)                     -- ^ Actual database of rules, to be searched
      , _chrgstNextFreeRuleInx       :: {-# UNPACK #-} !CHRInx                                          -- ^ Next free rule identification, used by solving to identify whether a rule has been used for a constraint.
                                                                                         --   The numbering is applied to constraints inside a rule which can be matched.
      , _chrgstScheduleQueue         :: !(Que.MinPQueue (CHRPrioEvaluatableVal bprio) (CHRMonoBacktrackPrioT cnstr guard bprio prio subst env m (SolverResult subst)))
      , _chrgstTrace                 :: !(SolveTrace' cnstr (StoredCHR cnstr guard bprio prio) subst)
      , _chrgstStatNrSolveSteps      :: {-# UNPACK #-} !Int
      , _chrgstVarToNmMp             :: !VarToNmMp
      }
  deriving (Typeable)

emptyCHRGlobState :: TT.TTCtxt (TT.TrTrKey c) => CHRGlobState c g b p s e m
emptyCHRGlobState = CHRGlobState emptyCHRStore 0 Que.empty emptySolveTrace 0 emptyVarToNmMp

-- | Backtrackable state
data CHRBackState cnstr bprio subst env
  = CHRBackState
      { _chrbstBacktrackPrio         :: !(CHRPrioEvaluatableVal bprio)                          -- ^ the current backtrack prio the solver runs on
      
      , _chrbstRuleWorkQueue         :: !WorkQueue                                              -- ^ work queue for rule matching
      , _chrbstSolveQueue            :: !WorkQueue                                              -- ^ solve queue, constraints which are not solved by rule matching but with some domain specific solver, yielding variable subst constributing to backtrackable bindings
      , _chrbstResidualQueue         :: [WorkInx]                                               -- ^ residual queue, constraints which are residual, no need to solve, etc
      , _chrbstWorkStore             :: !(WorkStore cnstr)                               -- ^ Actual database of solvable constraints
      
      , _chrbstMatchedCombis         :: !(Set.Set MatchedCombi)                                 -- ^ all combis of chr + work which were reduced, to prevent this from happening a second time (when propagating)
      
      , _chrbstFreshVar              :: {-# UNPACK #-} !Int                                                    -- ^ for fresh var
      , _chrbstSolveSubst            :: !subst                                                  -- ^ subst for variable bindings found during solving, not for the ones binding rule metavars during matching but for the user ones (in to be solved constraints)
      , _chrbstWaitForVar            :: !(Map.Map (VarLookupKey subst) [WaitForVar subst])       -- ^ work waiting for a var to be bound
      
      , _chrbstReductionSteps        :: ![SolverReductionStep]                                   -- ^ trace of reduction steps taken (excluding solve steps)
      }
  deriving (Typeable)

emptyCHRBackState :: (TT.TTCtxt (TT.TrTrKey c), CHREmptySubstitution s, Bounded (CHRPrioEvaluatableVal bp)) => CHRBackState c bp s e
emptyCHRBackState = CHRBackState minBound emptyWorkQueue emptyWorkQueue [] emptyWorkStore Set.empty 0 chrEmptySubst Map.empty []

-- | Monad for CHR, taking from 'LogicStateT' the state and backtracking behavior
type CHRMonoBacktrackPrioT cnstr guard bprio prio subst env m
  = LogicStateT (CHRGlobState cnstr guard bprio prio subst env m) (CHRBackState cnstr bprio subst env) m

-- | Full state as returned and used by running 'CHRMonoBacktrackPrioT'
type CHRFullState cnstr guard bprio prio subst env m
  = (CHRGlobState cnstr guard bprio prio subst env m, CHRBackState cnstr bprio subst env)

gst :: Lens (CHRFullState cnstr guard bprio prio subst env m) (CHRGlobState cnstr guard bprio prio subst env m)
gst = fstl
{-# INLINE gst #-}

bst :: Lens (CHRFullState cnstr guard bprio prio subst env m) (CHRBackState cnstr bprio subst env)
bst = sndl
{-# INLINE bst #-}

-- | All required behavior, as alias
type MonoBacktrackPrio cnstr guard bprio prio subst env m
    = ( IsCHRSolvable env cnstr guard bprio prio subst
      , Monad m
      -- TODO: replace MonadIO with API abstracting away access to persistent structures
      -- , MonadIO m
      , Lookup subst (VarLookupKey subst) (VarLookupVal subst)
      , LookupApply subst subst
      , Fresh Int (ExtrValVarKey (VarLookupVal subst))
      , ExtrValVarKey (VarLookupVal subst) ~ VarLookupKey subst
      , VarTerm (VarLookupVal subst)
      )

-------------------------------------------------------------------------------------------
--- Solver result
-------------------------------------------------------------------------------------------

-- | Solver solution
data SolverResult subst =
  SolverResult
    { slvresSubst                 :: !subst                            -- ^ global found variable bindings
    , slvresResidualCnstr         :: ![WorkInx]                        -- ^ constraints which are residual, no need to solve, etc, leftover when ready, taken from backtrack state
    , slvresWorkCnstr             :: ![WorkInx]                        -- ^ constraints which are still unsolved, taken from backtrack state
    , slvresWaitVarCnstr          :: ![WorkInx]                        -- ^ constraints which are still unsolved, waiting for variable resolution
    , slvresReductionSteps        :: ![SolverReductionStep]            -- ^ how did we get to the result (taken from the backtrack state when a result is given back)
    }

-------------------------------------------------------------------------------------------
--- Solver: required instances
-------------------------------------------------------------------------------------------

-- | Alias API for solving requirements
type IsCHRSolvable env c g bp p s
    = ( IsCHRConstraint env c s
      , IsCHRGuard env g s
      , IsCHRBacktrackPrio env bp s
      , IsCHRPrio env p s
      , PP (VarLookupKey s)
      ) 

-------------------------------------------------------------------------------------------
--- Lens construction
-------------------------------------------------------------------------------------------

mkLabel ''WaitForVar
mkLabel ''StoredCHR
mkLabel ''CHRStore
mkLabel ''WorkStore
mkLabel ''WorkQueue
mkLabel ''CHRGlobState
mkLabel ''CHRBackState

-------------------------------------------------------------------------------------------
--- Misc utils
-------------------------------------------------------------------------------------------

getSolveTrace :: (PP c, PP g, PP bp, MonoBacktrackPrio c g bp p s e m) => CHRMonoBacktrackPrioT c g bp p s e m PP_Doc
getSolveTrace = fmap (ppSolveTrace . reverse) $ getl $ gst ^* chrgstTrace

-------------------------------------------------------------------------------------------
--- CHR store, API for adding rules
-------------------------------------------------------------------------------------------

instance Show (StoredCHR c g bp p) where
  show _ = "StoredCHR"

ppStoredCHR :: (PP (TT.TrTrKey c), PP c, PP g, PP bp, PP p) => StoredCHR c g bp p -> PP_Doc
ppStoredCHR c@(StoredCHR {})
  = ppParensCommas (_storedHeadKeys c)
    >-< _storedChrRule c
    >-< indent 2
          (ppParensCommas
            [ pp $ _storedChrInx c
            -- , pp $ storedSimpSz c
            -- , "keys" >#< (ppBracketsCommas $ map (maybe (pp "?") ppTreeTrieKey) $ storedKeys c)
            -- , "ident" >#< ppParensCommas [ppTreeTrieKey idKey,pp idSeqNr]
            ])

instance (PP (TT.TrTrKey c), PP c, PP g, PP bp, PP p) => PP (StoredCHR c g bp p) where
  pp = ppStoredCHR

-- | Add a rule as a CHR
addRule :: MonoBacktrackPrio c g bp p s e m => Rule c g bp p -> CHRMonoBacktrackPrioT c g bp p s e m ()
addRule chr = do
    i <- modifyAndGet (gst ^* chrgstNextFreeRuleInx) $ \i -> (i, i + 1)
    let ks = map TT.toTreeTrieKey $ ruleHead chr
    gst ^* chrgstStore ^* chrstoreTable =$: IntMap.insert i (StoredCHR ks chr i)
    gst ^* chrgstStore ^* chrstoreTrie =$: \t ->
      foldr (TT.unionWith (++)) t [ TT.singleton k [CHRConstraintInx i j] | (k,c,j) <- zip3 ks (ruleHead chr) [0..] ]
    return ()


-- | Add work to the rule work queue
addToWorkQueue :: MonoBacktrackPrio c g bp p s e m => WorkInx -> CHRMonoBacktrackPrioT c g bp p s e m ()
addToWorkQueue i = do
    bst ^* chrbstRuleWorkQueue ^* wkqueueActive =$: (IntSet.insert i)
    bst ^* chrbstRuleWorkQueue ^* wkqueueDidSomething =: True
{-# INLINE addToWorkQueue #-}

-- | Add redo work to the rule work queue
addRedoToWorkQueue :: MonoBacktrackPrio c g bp p s e m => WorkInx -> CHRMonoBacktrackPrioT c g bp p s e m ()
addRedoToWorkQueue i = do
    bst ^* chrbstRuleWorkQueue ^* wkqueueRedo =$: (IntSet.insert i)
{-# INLINE addRedoToWorkQueue #-}

-- | Add work to the wait for var queue
addWorkToWaitForVarQueue :: (MonoBacktrackPrio c g bp p s e m, Ord (VarLookupKey s)) => CHRWaitForVarSet s -> WorkInx -> CHRMonoBacktrackPrioT c g bp p s e m ()
addWorkToWaitForVarQueue wfvs wi = do
    let w = WaitForVar wfvs wi
    bst ^* chrbstWaitForVar =$: Map.unionWith (++) (Map.fromList [(v,[w]) | v <- Set.toList wfvs])

-- | For (new) found subst split off work waiting for it
splitOffResolvedWaitForVarWork :: (MonoBacktrackPrio c g bp p s e m, Ord (VarLookupKey s)) => CHRWaitForVarSet s -> CHRMonoBacktrackPrioT c g bp p s e m [WorkInx]
splitOffResolvedWaitForVarWork vars = do
    -- wait admin
    wm <- getl $ bst ^* chrbstWaitForVar
    let -- split off the part which can be released
        (wmRelease,wmRemain) = Map.partitionWithKey (\v _ -> Set.member v vars) wm
        wfvs = concat $ Map.elems wmRelease
        -- get all influenced vars and released work
        (wvars, winxs) = (\(vss,wis) -> (Set.unions vss, IntSet.fromList wis)) $ unzip [ (vs,wi) | (WaitForVar {_waitForVarVars=vs, _waitForVarWorkInx=wi}) <- wfvs ]
    -- remove released work from remaining admin for influenced vars
    bst ^* chrbstWaitForVar =:
      foldr (Map.alter $ maybe Nothing $ \wfvs -> case filter (\i -> _waitForVarWorkInx i `IntSet.notMember` winxs) wfvs of
                [] -> Nothing
                wfvs' -> Just wfvs'
            )
            wmRemain
            (Set.toList wvars)

    -- released work
    return $ IntSet.toList winxs


-- | Add work to the solve queue
addWorkToSolveQueue :: MonoBacktrackPrio c g bp p s e m => WorkInx -> CHRMonoBacktrackPrioT c g bp p s e m ()
addWorkToSolveQueue i = do
    bst ^* chrbstSolveQueue ^* wkqueueActive =$: (IntSet.insert i)

-- | Split off work from the solve work queue, possible none left
splitWorkFromSolveQueue :: MonoBacktrackPrio c g bp p s e m => CHRMonoBacktrackPrioT c g bp p s e m (Maybe (WorkInx))
splitWorkFromSolveQueue = do
    wq <- getl $ bst ^* chrbstSolveQueue ^* wkqueueActive
    case IntSet.minView wq of
      Nothing ->
          return Nothing
      Just (workInx, wq') -> do
          bst ^* chrbstSolveQueue ^* wkqueueActive =: wq'
          return $ Just (workInx)

-- | Remove work from the work queue
deleteFromWorkQueue :: MonoBacktrackPrio c g bp p s e m => WorkInxSet -> CHRMonoBacktrackPrioT c g bp p s e m ()
deleteFromWorkQueue is = do
    -- bst ^* chrbstRuleWorkQueue ^* wkqueueActive =$: (\s -> foldr (IntSet.delete) s is)
    bst ^* chrbstRuleWorkQueue ^* wkqueueActive =$: flip IntSet.difference is
    bst ^* chrbstRuleWorkQueue ^* wkqueueRedo =$: flip IntSet.difference is

-- | Extract the active work in the queue
waitingInWorkQueue :: MonoBacktrackPrio c g bp p s e m => CHRMonoBacktrackPrioT c g bp p s e m WorkInxSet
waitingInWorkQueue = do
    a <- getl $ bst ^* chrbstRuleWorkQueue ^* wkqueueActive
    r <- getl $ bst ^* chrbstRuleWorkQueue ^* wkqueueRedo
    return $ IntSet.union a r

-- | Split off work from the work queue, possible none left
splitFromWorkQueue :: MonoBacktrackPrio c g bp p s e m => CHRMonoBacktrackPrioT c g bp p s e m (Maybe WorkInx)
splitFromWorkQueue = do
    wq <- getl $ bst ^* chrbstRuleWorkQueue ^* wkqueueActive
    case IntSet.minView wq of
      -- If no more work, ready if nothing was done anymore
      Nothing -> do
          did <- modifyAndGet (bst ^* chrbstRuleWorkQueue ^* wkqueueDidSomething) $ \d -> (d, False)
          if did -- && not (IntSet.null wr)
            then do
              wr  <- modifyAndGet (bst ^* chrbstRuleWorkQueue ^* wkqueueRedo) $ \r -> (r, IntSet.empty)
              bst ^* chrbstRuleWorkQueue ^* wkqueueActive =: wr
              splitFromWorkQueue
            else
              return Nothing
      
      -- There is work in the queue
      Just (workInx, wq') -> do
          bst ^* chrbstRuleWorkQueue ^* wkqueueActive =: wq'
          return $ Just workInx

-- | Add a constraint to be solved or residualised
addConstraintAsWork
  :: MonoBacktrackPrio c g bp p s e m
  => c
  -> CHRMonoBacktrackPrioT c g bp p s e m (ConstraintSolvesVia, WorkInx)
addConstraintAsWork c = do
    let via = cnstrSolvesVia c
        addw i w = do
          bst ^* chrbstWorkStore ^* wkstoreTable =$: IntMap.insert i w
          return (via,i)
    i <- fresh
    w <- case via of
        -- a plain rule is added to the work store
        ConstraintSolvesVia_Rule -> do
            bst ^* chrbstWorkStore ^* wkstoreTrie =$: TT.insertByKeyWith (++) k [i]
            addToWorkQueue i
            return $ Work k c i
          where k = TT.toTreeTrieKey c -- chrToKey c -- chrToWorkKey c
        -- work for the solver is added to its own queue
        ConstraintSolvesVia_Solve -> do
            addWorkToSolveQueue i
            return $ Work_Solve c
        -- residue is just remembered
        ConstraintSolvesVia_Residual -> do
            bst ^* chrbstResidualQueue =$: (i :)
            return $ Work_Residue c
        -- fail right away if this constraint is a fail constraint
        ConstraintSolvesVia_Fail -> do
            addWorkToSolveQueue i
            return Work_Fail
    addw i w
{-
        -- succeed right away if this constraint is a succes constraint
        -- TBD, different return value of slvSucces...
        ConstraintSolvesVia_Succeed -> do
            slvSucces
-}
  where
    fresh = modifyAndGet (bst ^* chrbstWorkStore ^* wkstoreNextFreeWorkInx) $ \i -> (i, i + 1)

-------------------------------------------------------------------------------------------
--- Solver combinators
-------------------------------------------------------------------------------------------

-- | Succesful return, solution is found
slvSucces :: MonoBacktrackPrio c g bp p s e m => [WorkInx] -> CHRMonoBacktrackPrioT c g bp p s e m (SolverResult s)
slvSucces leftoverWork = do
    bst <- getl $ bst
    let ret = return $ SolverResult
          { slvresSubst = bst ^. chrbstSolveSubst
          , slvresResidualCnstr = reverse $ bst ^. chrbstResidualQueue
          , slvresWorkCnstr = leftoverWork
          , slvresWaitVarCnstr = [ wfv ^. waitForVarWorkInx | wfvs <- Map.elems $ bst ^. chrbstWaitForVar, wfv <- wfvs ]
          , slvresReductionSteps = reverse $ bst ^. chrbstReductionSteps
          }
    -- when ready, just return and backtrack into the scheduler
    ret `mplus` slvScheduleRun

-- | Failure return, no solution is found
slvFail :: MonoBacktrackPrio c g bp p s e m => CHRMonoBacktrackPrioT c g bp p s e m (SolverResult s)
slvFail = do
    -- failing just terminates this slv, scheduling to another, if any
    slvScheduleRun
{-# INLINE slvFail #-}

-- | Schedule a solver with the current backtrack prio, assuming this is the same as 'slv' has administered itself in its backtracking state
slvSchedule :: MonoBacktrackPrio c g bp p s e m => CHRPrioEvaluatableVal bp -> CHRMonoBacktrackPrioT c g bp p s e m (SolverResult s) -> CHRMonoBacktrackPrioT c g bp p s e m ()
slvSchedule bprio slv = do
    -- bprio <- getl $ bst ^* chrbstBacktrackPrio
    gst ^* chrgstScheduleQueue =$: Que.insert bprio slv
{-# INLINE slvSchedule #-}

-- | Schedule a solver with the current backtrack prio, assuming this is the same as 'slv' has administered itself in its backtracking state
slvSchedule' :: MonoBacktrackPrio c g bp p s e m => CHRMonoBacktrackPrioT c g bp p s e m (SolverResult s) -> CHRMonoBacktrackPrioT c g bp p s e m ()
slvSchedule' slv = do
    bprio <- getl $ bst ^* chrbstBacktrackPrio
    slvSchedule bprio slv
{-# INLINE slvSchedule' #-}

-- | Rechedule a solver, switching context/prio
slvReschedule :: MonoBacktrackPrio c g bp p s e m => CHRMonoBacktrackPrioT c g bp p s e m (SolverResult s) -> CHRMonoBacktrackPrioT c g bp p s e m (SolverResult s)
slvReschedule slv = do
    slvSchedule' slv
    slvScheduleRun
{-# INLINE slvReschedule #-}

-- | Retrieve solver with the highest prio from the schedule queue
slvSplitFromSchedule :: MonoBacktrackPrio c g bp p s e m => CHRMonoBacktrackPrioT c g bp p s e m (Maybe (CHRPrioEvaluatableVal bp, CHRMonoBacktrackPrioT c g bp p s e m (SolverResult s)))
slvSplitFromSchedule = modifyAndGet (gst ^* chrgstScheduleQueue) $ \q -> (Que.getMin q, Que.deleteMin q)
{-# INLINE slvSplitFromSchedule #-}

-- | Run from the schedule que, fail if nothing left to be done
slvScheduleRun :: MonoBacktrackPrio c g bp p s e m => CHRMonoBacktrackPrioT c g bp p s e m (SolverResult s)
slvScheduleRun = slvSplitFromSchedule >>= maybe mzero snd
{-# INLINE slvScheduleRun #-}

-------------------------------------------------------------------------------------------
--- Solver utils
-------------------------------------------------------------------------------------------

lkupWork :: MonoBacktrackPrio c g bp p s e m => WorkInx -> CHRMonoBacktrackPrioT c g bp p s e m (Work c)
lkupWork i = fmap (IntMap.findWithDefault (panic "MBP.wkstoreTable.lookup") i) $ getl $ bst ^* chrbstWorkStore ^* wkstoreTable
{-# INLINE lkupWork #-}

lkupChr :: MonoBacktrackPrio c g bp p s e m => CHRInx -> CHRMonoBacktrackPrioT c g bp p s e m (StoredCHR c g bp p)
lkupChr  i = fmap (IntMap.findWithDefault (panic "MBP.chrSolve.chrstoreTable.lookup") i) $ getl $ gst ^* chrgstStore ^* chrstoreTable
{-# INLINE lkupChr #-}

-- | Convert
cvtSolverReductionStep :: MonoBacktrackPrio c g bp p s e m => SolverReductionStep' CHRInx WorkInx -> CHRMonoBacktrackPrioT c g bp p s e m (SolverReductionStep' (StoredCHR c g bp p) (Work c))
cvtSolverReductionStep (SolverReductionStep mc ai nw) = do
    mc  <- cvtMC mc
    nw  <- fmap Map.fromList $ forM (Map.toList nw) $ \(via,i) -> do
             i <- forM i lkupWork
             return (via, i)
    return $ SolverReductionStep mc ai nw
  where
    cvtMC (MatchedCombi {mcCHR = c, mcWork = ws}) = do
      c'  <- lkupChr c
      ws' <- forM ws lkupWork
      return $ MatchedCombi c' ws'
cvtSolverReductionStep (SolverReductionDBG pp) = return (SolverReductionDBG pp)

-- | PP result
ppSolverResult
  :: ( MonoBacktrackPrio c g bp p s e m
     , VarUpdatable s s
     , PP s
     ) => Verbosity
       -> SolverResult s
       -> CHRMonoBacktrackPrioT c g bp p s e m PP_Doc
ppSolverResult verbosity (SolverResult {slvresSubst = s, slvresResidualCnstr = ris, slvresWorkCnstr = wis, slvresWaitVarCnstr = wvis, slvresReductionSteps = steps}) = do
    let lk i = lkupWork i >>= return . pp . workCnstr
    rs  <- forM ris  lk
    ws  <- forM wis  lk
    wvs <- forM wvis lk
    ss  <- if verbosity >= Verbosity_ALot
      then forM steps $ \step -> cvtSolverReductionStep step >>= (return . pp)
      else return [pp $ "Only included with enough verbosity turned on"]
    nrsteps <- getl $ gst ^* chrgstStatNrSolveSteps
    let pextra | verbosity >= Verbosity_Normal = 
                      "Residue" >-< indent 2 (vlist rs)
                  >-< "Wait"    >-< indent 2 (vlist wvs)
                  >-< "Stats"   >-< indent 2 (ppAssocLV [ ("Count of overall solve steps", pp nrsteps) ])
                  >-< "Steps"   >-< indent 2 (vlist ss)
               | otherwise = Pretty.empty
    return $ 
          "Subst"   >-< indent 2 (s `varUpd` s)
      >-< "Work"    >-< indent 2 (vlist ws)
      >-< pextra

-------------------------------------------------------------------------------------------
--- Solver: running it
-------------------------------------------------------------------------------------------

-- | Run and observe results
runCHRMonoBacktrackPrioT
  :: MonoBacktrackPrio cnstr guard bprio prio subst env m
     => CHRGlobState cnstr guard bprio prio subst env m
     -> CHRBackState cnstr bprio subst env
     -> CHRMonoBacktrackPrioT cnstr guard bprio prio subst env m (SolverResult subst)
     -> m ([SolverResult subst], (CHRGlobState cnstr guard bprio prio subst env m, CHRBackState cnstr bprio subst env))
runCHRMonoBacktrackPrioT gs bs {- bp -} m = observeStateAllT (gs, bs {- _chrbstBacktrackPrio=bp -}) m
{-# INLINABLE runCHRMonoBacktrackPrioT #-}

-------------------------------------------------------------------------------------------
--- Solver: Intermediate structures
-------------------------------------------------------------------------------------------

-- | Intermediate Solver structure
data FoundChr c g bp p
  = FoundChr
      { foundChrInx             :: {-# UNPACK #-} !CHRInx
      , foundChrChr             :: !(StoredCHR c g bp p)
      , foundChrCnstr           :: ![WorkInx]
      }

-- | Intermediate Solver structure
data FoundWorkInx c g bp p
  = FoundWorkInx
      { foundWorkInxInx         :: {-# UNPACK #-} !CHRConstraintInx
      , foundWorkInxChr         :: !(StoredCHR c g bp p)
      , foundWorkInxWorkInxs    :: ![[WorkInx]]
      }

-- | Intermediate Solver structure: sorting key for matches
data FoundMatchSortKey bp p s
  = FoundMatchSortKey
      { foundMatchSortKeyPrio           :: !(Maybe (s,p))
      , foundMatchSortKeyWaitSize       :: {-# UNPACK #-} !Int
      , foundMatchSortKeyTextOrder      :: {-# UNPACK #-} !CHRInx
      }

instance Show (FoundMatchSortKey bp p s) where
  show _ = "FoundMatchSortKey"

instance (PP p, PP s) => PP (FoundMatchSortKey bp p s) where
  pp (FoundMatchSortKey {foundMatchSortKeyPrio=p, foundMatchSortKeyWaitSize=w, foundMatchSortKeyTextOrder=o}) = ppParensCommas [pp p, pp w, pp o]

compareFoundMatchSortKey :: {- (Ord (CHRPrioEvaluatableVal bp)) => -} ((s,p) -> (s,p) -> Ordering) -> FoundMatchSortKey bp p s -> FoundMatchSortKey bp p s -> Ordering
compareFoundMatchSortKey cmp_rp (FoundMatchSortKey {- bp1 -} rp1 ws1 to1) (FoundMatchSortKey {- bp2 -} rp2 ws2 to2) =
    {- orderingLexic (bp1 `compare` bp2) $ -} orderingLexic (rp1 `cmp_mbrp` rp2) $ orderingLexic (ws1 `compare` ws2) $ to1 `compare` to2
  where
    cmp_mbrp (Just rp1) (Just rp2) = cmp_rp rp1 rp2
    cmp_mbrp (Just _  ) _          = GT
    cmp_mbrp _          (Just _  ) = LT
    cmp_mbrp _          _          = EQ

-- | Intermediate Solver structure: body alternative, together with index position
data FoundBodyAlt c bp
  = FoundBodyAlt
      { foundBodyAltInx             :: {-# UNPACK #-} !Int
      , foundBodyAltBacktrackPrio   :: !(CHRPrioEvaluatableVal bp)
      , foundBodyAltAlt             :: !(RuleBodyAlt c bp)
      }

instance Show (FoundBodyAlt c bp) where
  show _ = "FoundBodyAlt"

instance (PP c, PP bp, PP (CHRPrioEvaluatableVal bp)) => PP (FoundBodyAlt c bp) where
  pp (FoundBodyAlt {foundBodyAltInx=i, foundBodyAltBacktrackPrio=bp, foundBodyAltAlt=a}) = i >|< ":" >|< ppParens bp >#< a

-- | Intermediate Solver structure: all matched combis with their body alternatives + backtrack priorities
data FoundSlvMatch c g bp p s
  = FoundSlvMatch
      { foundSlvMatchSubst          :: !s                                   -- ^ the subst of rule meta vars making this a rule + work combi match
      , foundSlvMatchFreeVars       :: !(CHRWaitForVarSet s)                -- ^ free meta vars of head
      , foundSlvMatchWaitForVars    :: !(CHRWaitForVarSet s)                -- ^ for the work we try to solve the (global) vars on which we have to wait to continue
      , foundSlvMatchSortKey        :: !(FoundMatchSortKey bp p s)          -- ^ key to sort found matches
      , foundSlvMatchBodyAlts       :: ![FoundBodyAlt c bp]                 -- ^ the body alternatives of the rule which matches
      }

instance Show (FoundSlvMatch c g bp p s) where
  show _ = "FoundSlvMatch"

instance (PP s, PP p, PP c, PP bp, PP (VarLookupKey s), PP (CHRPrioEvaluatableVal bp)) => PP (FoundSlvMatch c g bp p s) where
  pp (FoundSlvMatch {foundSlvMatchSubst=s, foundSlvMatchWaitForVars=ws, foundSlvMatchBodyAlts=as}) = ws >#< s >-< vlist as

-- | Intermediate Solver structure: all matched combis with their backtrack prioritized body alternatives
data FoundWorkMatch c g bp p s
  = FoundWorkMatch
      { foundWorkMatchInx       :: {-# UNPACK #-} !CHRConstraintInx
      , foundWorkMatchChr       :: !(StoredCHR c g bp p)
      , foundWorkMatchWorkInx   :: ![WorkInx]
      , foundWorkMatchSlvMatch  :: !(Maybe (FoundSlvMatch c g bp p s))
      }

instance Show (FoundWorkMatch c g bp p s) where
  show _ = "FoundWorkMatch"

instance (PP c, PP bp, PP p, PP s, PP (VarLookupKey s), PP (CHRPrioEvaluatableVal bp)) => PP (FoundWorkMatch c g bp p s) where
  pp (FoundWorkMatch {foundWorkMatchSlvMatch=sm}) = pp sm

-- | Intermediate Solver structure: all matched combis with their backtrack prioritized body alternatives
data FoundWorkSortedMatch c g bp p s
  = FoundWorkSortedMatch
      { foundWorkSortedMatchInx             :: !CHRConstraintInx
      , foundWorkSortedMatchChr             :: !(StoredCHR c g bp p)
      , foundWorkSortedMatchBodyAlts        :: ![FoundBodyAlt c bp]
      , foundWorkSortedMatchWorkInx         :: ![WorkInx]
      , foundWorkSortedMatchSubst           :: !s
      , foundWorkSortedMatchFreeVars        :: !(CHRWaitForVarSet s)
      , foundWorkSortedMatchWaitForVars     :: !(CHRWaitForVarSet s)
      }

instance Show (FoundWorkSortedMatch c g bp p s) where
  show _ = "FoundWorkSortedMatch"

instance (PP c, PP bp, PP p, PP s, PP g, PP (VarLookupKey s), PP (CHRPrioEvaluatableVal bp)) => PP (FoundWorkSortedMatch c g bp p s) where
  pp (FoundWorkSortedMatch {foundWorkSortedMatchBodyAlts=as, foundWorkSortedMatchWorkInx=wis, foundWorkSortedMatchSubst=s, foundWorkSortedMatchWaitForVars=wvs})
    = wis >-< s >#< ppParens wvs >-< vlist as

-------------------------------------------------------------------------------------------
--- Solver options
-------------------------------------------------------------------------------------------

-- | Solve specific options
data CHRSolveOpts
  = CHRSolveOpts
      { chrslvOptSucceedOnLeftoverWork  :: !Bool        -- ^ left over unresolvable (non residue) work is also a successful result
      , chrslvOptSucceedOnFailedSolve   :: !Bool        -- ^ failed solve is considered also a successful result, with the failed constraint as a residue
      , chrslvOptGatherDebugInfo        :: !Bool        -- ^ gather debug info
      , chrslvOptGatherTraceInfo        :: !Bool        -- ^ gather trace info
      }

defaultCHRSolveOpts :: CHRSolveOpts
defaultCHRSolveOpts
  = CHRSolveOpts
      { chrslvOptSucceedOnLeftoverWork  = False
      , chrslvOptSucceedOnFailedSolve   = False
      , chrslvOptGatherDebugInfo        = False
      , chrslvOptGatherTraceInfo        = False
      }

-------------------------------------------------------------------------------------------
--- Solver
-------------------------------------------------------------------------------------------

{-# INLINABLE chrSolve #-}
-- | (Under dev) solve
chrSolve
  :: forall c g bp p s e m .
     ( MonoBacktrackPrio c g bp p s e m
     , PP s
     ) => CHRSolveOpts
       -> e
       -> CHRMonoBacktrackPrioT c g bp p s e m (SolverResult s)
chrSolve opts env = slv
  where
    -- gather debug info
    dbg | chrslvOptGatherDebugInfo opts = \i -> bst ^* chrbstReductionSteps =$: (SolverReductionDBG i :)
        | otherwise                     = \_ -> return ()
    -- gather trace info
    trc | chrslvOptGatherTraceInfo opts = \i -> gst ^* chrgstTrace =$: (i :)
        | otherwise                     = \_ -> return ()
    -- leave this unconditional, does not seem not make a difference for performance
    -- trc i = gst ^* chrgstTrace =$: (i :)
    -- solve
    slv = do
        gst ^* chrgstStatNrSolveSteps =$: (+1)
        mbSlvWk <- splitWorkFromSolveQueue
        case mbSlvWk of
          -- There is work in the solve work queue
          Just (workInx) -> do
              work <- lkupWork workInx
              case work of
                Work_Fail -> slvFail
                _ -> do
                  subst <- getl $ bst ^* chrbstSolveSubst
                  let mbSlv = chrmatcherRun (chrBuiltinSolveM env $ workCnstr work) emptyCHRMatchEnv subst
                  
                  -- debug info
                  dbg $ 
                    (    "solve wk" >#< work
                     >-< "match" >#< mbSlv
                    )

                  case mbSlv of
                    Just (s,_) -> do
                          -- the newfound subst may reactivate waiting work
                          splitOffResolvedWaitForVarWork (Lk.keysSet s) >>= mapM_ addToWorkQueue
                          bst ^* chrbstSolveSubst =$: (s `Lk.apply`)
                          -- just continue with next work
                          slv
                    _ | chrslvOptSucceedOnFailedSolve opts -> do
                          bst ^* chrbstResidualQueue =$: (workInx :)
                          -- just continue with next work
                          slv
                      | otherwise -> do
                          slvFail


          -- If no more solve work, continue with normal work
          Nothing -> do
              waitingWk <- waitingInWorkQueue
              visitedChrWkCombis <- getl $ bst ^* chrbstMatchedCombis
              mbWk <- splitFromWorkQueue
              case mbWk of
                -- If no more work, ready or cannot proceed
                Nothing -> do
                    wr <- getl $ bst ^* chrbstRuleWorkQueue ^* wkqueueRedo
                    if chrslvOptSucceedOnLeftoverWork opts || IntSet.null wr
                      then slvSucces $ IntSet.toList wr
                      else slvFail
      
                -- There is work in the queue
                Just workInx -> do
                    -- lookup the work
                    work  <- lkupWork  workInx
                    -- work2 <- lkupWork workInx
          
                    -- find all matching chrs for the work
                    foundChrInxs  <- slvLookup  (workKey work ) (gst ^* chrgstStore ^* chrstoreTrie )
                    -- foundChrInxs2 <- slvLookup2 (workKey work2) (chrgstStore ^* chrstoreTrie2)
                    -- remove duplicates, regroup
                    let foundChrGroupedInxs = Map.unionsWith Set.union $ map (\(CHRConstraintInx i j) -> Map.singleton i (Set.singleton j)) foundChrInxs
                    foundChrs <- forM (Map.toList foundChrGroupedInxs) $ \(chrInx,rlInxs) -> lkupChr chrInx >>= \chr -> return $ FoundChr chrInx chr $ Set.toList rlInxs

                    -- found chrs for the work correspond to 1 single position in the head, find all combinations with work in the queue
                    foundWorkInxs <- sequence
                      [ fmap (FoundWorkInx (CHRConstraintInx ci i) c) $ slvCandidate waitingWk visitedChrWkCombis workInx c i
                      | FoundChr ci c is <- foundChrs, i <- is
                      ]
          
                    -- each found combi has to match
                    foundWorkMatches <- fmap concat $
                      forM foundWorkInxs $ \(FoundWorkInx ci c wis) -> do
                        forM wis $ \wi -> do
                          w <- forM wi lkupWork
                          fmap (FoundWorkMatch ci c wi) $ slvMatch env c (map workCnstr w) (chrciAt ci)

                    -- split off the work which has to wait for variable bindings (as indicated by matching)
                    -- sort over priorities
                    let foundWorkSortedMatches = sortByOn (compareFoundMatchSortKey $ chrPrioCompare env) fst
                          [ (k, FoundWorkSortedMatch
                                  { foundWorkSortedMatchInx         = foundWorkMatchInx fwm
                                  , foundWorkSortedMatchChr         = foundWorkMatchChr fwm
                                  , foundWorkSortedMatchBodyAlts    = foundSlvMatchBodyAlts sm
                                  , foundWorkSortedMatchWorkInx     = foundWorkMatchWorkInx fwm
                                  , foundWorkSortedMatchSubst       = foundSlvMatchSubst sm
                                  , foundWorkSortedMatchFreeVars    = foundSlvMatchFreeVars sm
                                  , foundWorkSortedMatchWaitForVars = foundSlvMatchWaitForVars sm
                                  }
                            )
                          | fwm@(FoundWorkMatch {foundWorkMatchSlvMatch = Just sm@(FoundSlvMatch {foundSlvMatchSortKey=k})}) <- foundWorkMatches
                          ]

                    bprio <- getl $ bst ^* chrbstBacktrackPrio
                    subst <- getl $ bst ^* chrbstSolveSubst
                    dbgWaitInfo <- getl $ bst ^* chrbstWaitForVar
                    -- sque <- getl $ gst ^* chrgstScheduleQueue
                    -- debug info
                    dbg $          "bprio" >#< bprio
                               >-< "wk" >#< (work >-< subst `varUpd` workCnstr work)
                               >-< "que" >#< ppBracketsCommas (IntSet.toList waitingWk)
                               >-< "subst" >#< subst
                               >-< "wait" >#< ppAssocL (assocLMapElt (ppAssocL . map (\i -> (_waitForVarWorkInx i, ppCommas $ Set.toList $ _waitForVarVars i))) $ Map.toList dbgWaitInfo)
                               >-< "visited" >#< ppBracketsCommas (Set.toList visitedChrWkCombis)
                               >-< "chrs" >#< vlist [ ci >|< ppParensCommas is >|< ":" >#< c | FoundChr ci c is <- foundChrs ]
                               >-< "works" >#< vlist [ ci >|< ":" >#< vlist (map ppBracketsCommas ws) | FoundWorkInx ci c ws <- foundWorkInxs ]
                               >-< "matches" >#< vlist [ ci >|< ":" >#< ppBracketsCommas wi >#< ":" >#< mbm | FoundWorkMatch ci _ wi mbm <- foundWorkMatches ]
                               -- >-< "prio'd" >#< (vlist $ zipWith (\g ms -> g >|< ":" >#< vlist [ ci >|< ":" >#< ppBracketsCommas wi >#< ":" >#< s | (ci,_,wi,s) <- ms ]) [0::Int ..] foundWorkMatchesFilteredPriod)
                               -- >-< "prio'd" >#< ppAssocL (zip [0::Int ..] $ map ppAssocL foundWorkSortedMatches)

                    -- pick the first and highest rule prio solution
                    case break (Set.null . foundWorkSortedMatchWaitForVars) $ map snd foundWorkSortedMatches of
                      (_, fwsm:_) -> do
                            -- addRedoToWorkQueue workInx
                            addToWorkQueue workInx
                            slv1 bprio fwsm
                      ((FoundWorkSortedMatch {foundWorkSortedMatchWaitForVars = waitForVars}):_, _) -> do
                            -- put on wait queue if there are unresolved variables
                            addWorkToWaitForVarQueue waitForVars workInx
                            -- continue without reschedule
                            slv
                      _ -> do
                            addRedoToWorkQueue workInx
                            slv
{-
                      _ | chrslvOptSucceedOnLeftoverWork opts -> do
                            -- no chr applies for this work, so consider it to be residual
                            bst ^* chrbstLeftWorkQueue =$: (workInx :)
                            -- continue without reschedule
                            slv
                        | otherwise -> do
                            -- no chr applies for this work, can never be resolved, consider this a failure unless prevented by option
                            slvFail
-}

    -- solve one step further, allowing a backtrack point here
    slv1 curbprio
         (FoundWorkSortedMatch
            { foundWorkSortedMatchInx = CHRConstraintInx {chrciInx = ci}
            , foundWorkSortedMatchChr = chr@StoredCHR {_storedChrRule = Rule {ruleSimpSz = simpSz}}
            , foundWorkSortedMatchBodyAlts = alts
            , foundWorkSortedMatchWorkInx = workInxs
            , foundWorkSortedMatchSubst = matchSubst
            , foundWorkSortedMatchFreeVars = freeHeadVars
            }) = do
        -- remove the simplification part from the work queue
        deleteFromWorkQueue $ IntSet.fromList $ take simpSz workInxs
        -- depending on nr of alts continue slightly different
        case alts of
          -- just continue if no alts 
          [] -> do
            log Nothing
            slv
          -- just reschedule
          [alt@(FoundBodyAlt {foundBodyAltBacktrackPrio=bprio})]
            | curbprio == bprio -> do
                log (Just alt)
                nextwork bprio alt
            | otherwise -> do
                log (Just alt)
                slvSchedule bprio $ nextwork bprio alt
                slvScheduleRun
          -- otherwise backtrack and schedule all and then reschedule
          alts -> do
                forM alts $ \alt@(FoundBodyAlt {foundBodyAltBacktrackPrio=bprio}) -> do
                  log (Just alt)
                  (backtrackWithRoll (\_ _ bs -> {- (liftIO $ putStrLn "TEST") >> -} return bs) $ nextwork bprio alt) >>= slvSchedule bprio
                slvScheduleRun

      where
        log alt = do
          let a = (fmap (rbodyaltBody . foundBodyAltAlt) alt)
          trc $ SolveStep chr matchSubst a [] [] -- TODO: Set stepNewTodo, stepNewDone (last two arguments)
        nextwork bprio alt@(FoundBodyAlt {foundBodyAltAlt=(RuleBodyAlt {rbodyaltBody=body})}) = do
          -- set prio for this alt
          bst ^* chrbstBacktrackPrio =: bprio
          -- fresh vars for unbound body metavars
          freshSubst <- slvFreshSubst freeHeadVars body
          -- add each constraint from the body, applying the meta var subst
          newWkInxs <- forM body $ addConstraintAsWork . ((freshSubst `Lk.apply` matchSubst) `varUpd`)
          -- mark this combi of chr and work as visited
          let matchedCombi = MatchedCombi ci workInxs
          bst ^* chrbstMatchedCombis =$: Set.insert matchedCombi
          -- add this reduction step as being taken
          bst ^* chrbstReductionSteps =$: (SolverReductionStep matchedCombi (foundBodyAltInx alt) (Map.unionsWith (++) $ map (\(k,v) -> Map.singleton k [v]) $ newWkInxs) :)
          -- take next step
          slv

    -- misc utils

-- | Fresh variables in the form of a subst
slvFreshSubst
  :: forall c g bp p s e m x .
     ( MonoBacktrackPrio c g bp p s e m
     , ExtrValVarKey x ~ ExtrValVarKey (VarLookupVal s)
     , VarExtractable x
     ) => Set.Set (ExtrValVarKey x)
       -> x
       -> CHRMonoBacktrackPrioT c g bp p s e m s
slvFreshSubst except x = 
    fmap (foldr Lk.apply Lk.empty) $
      forM (Set.toList $ varFreeSet x `Set.difference` except) $ \v ->
        modifyAndGet (bst ^* chrbstFreshVar) (freshWith $ Just v) >>= \v' -> return $ (Lk.singleton v (varTermMkKey v') :: s)
{-# INLINE slvFreshSubst #-}

-- | Lookup work in a store part of the global state
slvLookup
  :: ( MonoBacktrackPrio c g bp p s e m
     , Ord (TT.TrTrKey c)
     ) => CHRKey c                                   -- ^ work key
       -> Lens (CHRGlobState c g bp p s e m, CHRBackState c bp s e) (TT.TreeTrie (TT.TrTrKey c) [x])
       -> CHRMonoBacktrackPrioT c g bp p s e m [x]
slvLookup key t =
    (getl t) >>= \t -> do
      return $ concat $ TT.lookupResultToList $ TT.lookup key t
{-# INLINE slvLookup #-}

-- | Extract candidates matching a CHRKey.
--   Return a list of CHR matches,
--     each match expressed as the list of constraints (in the form of Work + Key) found in the workList wlTrie, thus giving all combis with constraints as part of a CHR,
--     partititioned on before or after last query time (to avoid work duplication later)
slvCandidate
  :: forall c g bp p s e m
   . ( MonoBacktrackPrio c g bp p s e m
     ) => WorkInxSet                           -- ^ active in queue
       -> Set.Set MatchedCombi                      -- ^ already matched combis
       -> WorkInx                                   -- ^ work inx
       -> StoredCHR c g bp p                        -- ^ found chr for the work
       -> Int                                       -- ^ position in the head where work was found
       -> CHRMonoBacktrackPrioT c g bp p s e m
            ( [[WorkInx]]                           -- All matches of the head, unfiltered w.r.t. deleted work
            )
slvCandidate waitingWk alreadyMatchedCombis wi (StoredCHR {_storedHeadKeys = ks, _storedChrInx = ci}) headInx = do
    let [ks1,_,ks2] = splitPlaces [headInx, headInx+1] ks
    ws1 <- forM ks1 lkup
    ws2 <- forM ks2 lkup
    return $ filter (\wi ->    all (`IntSet.member` waitingWk) wi
                            && Set.notMember (MatchedCombi ci wi) alreadyMatchedCombis)
           $ combineToDistinguishedEltsBy (==) $ ws1 ++ [[wi]] ++ ws2
  where
    -- lkup :: CHRKey c -> CHRMonoBacktrackPrioT c g bp p s e m [WorkInx]
    lkup k = slvLookup k (bst ^* chrbstWorkStore ^* wkstoreTrie)
{-# INLINE slvCandidate #-}

-- | Match the stored CHR with a set of possible constraints, giving a substitution on success
slvMatch
  :: forall c g bp p s env m
   . ( MonoBacktrackPrio c g bp p s env m
     -- these below should not be necessary as they are implied (via superclasses) by MonoBacktrackPrio, but deeper nested superclasses seem not to be picked up...
     , CHRMatchable env c s
     , CHRCheckable env g s
     , CHRMatchable env bp s
     , CHRPrioEvaluatable env bp s
     ) => env
       -> StoredCHR c g bp p
       -> [c]
       -> Int                                       -- ^ position in the head where work was found, on that work specifically we might have to wait
       -> CHRMonoBacktrackPrioT c g bp p s env m (Maybe (FoundSlvMatch c g bp p s))
slvMatch env chr@(StoredCHR {_storedChrRule = Rule {rulePrio = mbpr, ruleHead = hc, ruleGuard = gd, ruleBacktrackPrio = mbbpr, ruleBodyAlts = alts}}) cnstrs headInx = do
    subst <- getl $ bst ^* chrbstSolveSubst
    curbprio <- fmap (chrPrioLift (Proxy :: Proxy env) (Proxy :: Proxy s)) $ getl $ bst ^* chrbstBacktrackPrio
    return $ fmap (\(s,ws) -> FoundSlvMatch s freevars ws (FoundMatchSortKey (fmap ((,) s) mbpr) (Set.size ws) (_storedChrInx chr))
                    [ FoundBodyAlt i bp a | (i,a) <- zip [0..] alts, let bp = maybe minBound (chrPrioEval env s) $ rbodyaltBacktrackPrio a
                    ])
           $ (\m -> chrmatcherRun m (emptyCHRMatchEnv {chrmatchenvMetaMayBind = (`Set.member` freevars)}) subst)
           $ sequence_
           $ prio curbprio ++ matches ++ checks
  where
    prio curbprio = maybe [] (\bpr -> [chrMatchToM env bpr curbprio]) mbbpr
    matches = zipWith3 (\i h c -> chrMatchAndWaitToM (i == headInx) env h c) [0::Int ..] hc cnstrs
    -- ignoreWait 
    checks  = map (chrCheckM env) gd
    freevars = Set.unions [varFreeSet hc, maybe Set.empty varFreeSet mbbpr]
{-# INLINE slvMatch #-}

