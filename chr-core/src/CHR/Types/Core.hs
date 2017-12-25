{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies, UndecidableInstances, ExistentialQuantification, ScopedTypeVariables, StandaloneDeriving, GeneralizedNewtypeDeriving, TemplateHaskell, NoMonomorphismRestriction #-}

-------------------------------------------------------------------------------------------
--- Constraint Handling Rules
-------------------------------------------------------------------------------------------

{- |
Derived from work by Gerrit vd Geest, but with searching structures for predicates
to avoid explosion of search space during resolution.
-}

module CHR.Types.Core
  ( IsConstraint(..)
  , ConstraintSolvesVia(..)

  , IsCHRConstraint(..)
  -- , CHRConstraint(..)
  
  , IsCHRGuard(..)
  -- , CHRGuard(..)
  
  -- , IsCHRBuiltin(..)
  -- , CHRBuiltin(..)
  
  , IsCHRPrio(..)
  -- , CHRPrio(..)
  
  , IsCHRBacktrackPrio(..)
  
  , CHREmptySubstitution(..)
  
  , CHRMatcherFailure(..)
  
  , CHRMatcher
  , chrmatcherRun'
  , chrmatcherRun
  -- , chrmatcherLift
  -- , chrmatcherUnlift
  
  , chrmatcherstateEnv
  , chrmatcherstateVarLookup
  
  , chrMatchResolveCompareAndContinue
  , chrMatchSubst
  , chrMatchBind
  , chrMatchFail
  , chrMatchFailNoBinding
  , chrMatchSuccess
  , chrMatchWait
  , chrMatchSucces
  -- , chrMatchVarUpd
  
  , CHRMatchEnv(..)
  , emptyCHRMatchEnv
  
  , CHRMatchable(..)
  , CHRMatchableKey
  , CHRMatchHow(..)
  , chrMatchAndWaitToM
  
  , CHRWaitForVarSet
  
  , CHRCheckable(..)
  
  , Prio(..)
  , CHRPrioEvaluatable(..)
  , CHRPrioEvaluatableVal
  
  -- , CHRBuiltinSolvable(..)
  
  , CHRTrOpt(..)
  
  , IVar
  
  , VarToNmMp
  , emptyVarToNmMp
  
  , NmToVarMp
  , emptyNmToVarMp
  )
  where

-- import qualified UHC.Util.TreeTrie as TreeTrie
import           CHR.Data.VarMp
import           CHR.Data.Lookup            (Lookup, Stacked, LookupApply)
import qualified CHR.Data.Lookup            as Lk
import qualified CHR.Data.Lookup.Stacked    as Lk
import qualified Data.Map.Strict            as Map
import qualified Data.HashMap.Strict        as MapH
import qualified Data.IntMap.Strict         as IntMap
import           Data.Word
import           Data.Monoid
import           Data.Typeable
import           Data.Function
import           Unsafe.Coerce
import qualified Data.Set as Set
import           CHR.Pretty
-- import           UHC.Util.CHR.Key
import qualified CHR.Data.TreeTrie          as TT
import           Control.Monad
import           Control.Monad.State -- .Strict
import           Control.Monad.Except
import           Control.Monad.Identity
import           CHR.Data.Lens
import           CHR.Utils
-- import           UHC.Util.Binary
-- import           UHC.Util.Serialize
import           CHR.Data.Substitutable

-- import           UHC.Util.Debug

-------------------------------------------------------------------------------------------
--- Name <-> Var mapping
-------------------------------------------------------------------------------------------

type IVar      = IntMap.Key

type VarToNmMp = IntMap.IntMap   String
type NmToVarMp = MapH.HashMap    String  IVar

emptyVarToNmMp :: VarToNmMp = IntMap.empty
emptyNmToVarMp :: NmToVarMp = MapH.empty

-------------------------------------------------------------------------------------------
--- CHRMatchHow
-------------------------------------------------------------------------------------------

-- | How to match, increasingly more binding is allowed
data CHRMatchHow
  = CHRMatchHow_Check               -- ^ equality check only
  | CHRMatchHow_Match               -- ^ also allow one-directional (left to right) matching/binding of (meta)vars
  | CHRMatchHow_MatchAndWait        -- ^ also allow giving back of global vars on which we wait
  | CHRMatchHow_Unify               -- ^ also allow bi-directional matching, i.e. unification
  deriving (Ord, Eq)

-------------------------------------------------------------------------------------------
--- CHRMatchEnv
-------------------------------------------------------------------------------------------

-- | Context/environment required for matching itself
data CHRMatchEnv k
  = CHRMatchEnv
      { {- chrmatchenvHow          :: !CHRMatchHow
      , -} 
        chrmatchenvMetaMayBind  :: !(k -> Bool)
      }

emptyCHRMatchEnv :: CHRMatchEnv x
emptyCHRMatchEnv = CHRMatchEnv {- CHRMatchHow_Check -} (const True)

-------------------------------------------------------------------------------------------
--- Wait for var
-------------------------------------------------------------------------------------------

type CHRWaitForVarSet s = Set.Set (VarLookupKey s)

-------------------------------------------------------------------------------------------
--- CHRMatcher, call back API used during matching
-------------------------------------------------------------------------------------------

{-
data CHRMatcherState subst k
  = CHRMatcherState
      { _chrmatcherstateVarLookup       :: !(StackedVarLookup subst)
      , _chrmatcherstateWaitForVarSet   :: !(CHRWaitForVarSet subst)
      , _chrmatcherstateEnv             :: !(CHRMatchEnv k)
      }
  deriving Typeable
-}
type CHRMatcherState subst k = (StackedVarLookup subst, CHRWaitForVarSet (Lk.StackedElt (StackedVarLookup subst)), CHRMatchEnv k)

mkCHRMatcherState :: StackedVarLookup subst -> CHRWaitForVarSet (Lk.StackedElt (StackedVarLookup subst)) -> CHRMatchEnv k -> CHRMatcherState subst k
mkCHRMatcherState s w e = (s, w, e)
-- mkCHRMatcherState s w e = CHRMatcherState s w e
{-# INLINE mkCHRMatcherState #-}

unCHRMatcherState :: CHRMatcherState subst k -> (StackedVarLookup subst, CHRWaitForVarSet (Lk.StackedElt (StackedVarLookup subst)), CHRMatchEnv k)
unCHRMatcherState = id
-- unCHRMatcherState (CHRMatcherState s w e) = (s,w,e)
{-# INLINE unCHRMatcherState #-}

-- | Failure of CHRMatcher
data CHRMatcherFailure
  = CHRMatcherFailure
  | CHRMatcherFailure_NoBinding         -- ^ absence of binding

-- | Matching monad, keeping a stacked (pair) of subst (local + global), and a set of global variables upon which the solver has to wait in order to (possibly) match further/again
-- type CHRMatcher subst = StateT (StackedVarLookup subst, CHRWaitForVarSet subst) (Either ())
type CHRMatcher subst = StateT (CHRMatcherState subst (VarLookupKey subst)) (Either CHRMatcherFailure)

-- instance (k ~ VarLookupKey subst) => MonadState (CHRMatcherState subst k) (CHRMatcher subst)

chrmatcherstateVarLookup     = fst3l
chrmatcherstateWaitForVarSet = snd3l
chrmatcherstateEnv           = trd3l

{-
mkLabel ''CHRMatcherState
-}

-------------------------------------------------------------------------------------------
--- Common part w.r.t. variable lookup
-------------------------------------------------------------------------------------------

-- | Do the resolution part of a comparison, continuing with a function which can assume variable resolution has been done for the terms being compared
chrMatchResolveCompareAndContinue
  :: forall s .
     ( Lookup s (VarLookupKey s) (VarLookupVal s)
     , LookupApply s s
     , Ord (VarLookupKey s)
     , VarTerm (VarLookupVal s)
     , ExtrValVarKey (VarLookupVal s) ~ VarLookupKey s
     )
  =>    CHRMatchHow                                                     -- ^ how to do the resolution
     -> (VarLookupVal s -> VarLookupVal s -> CHRMatcher s ())           -- ^ succeed with successful varlookup continuation
     -> VarLookupVal s                                                  -- ^ left/fst val
     -> VarLookupVal s                                                  -- ^ right/snd val
     -> CHRMatcher s ()
chrMatchResolveCompareAndContinue how ok t1 t2
  = cmp t1 t2
  where cmp t1 t2 = do
          menv <- getl chrmatcherstateEnv
          case (varTermMbKey t1, varTermMbKey t2) of
              (Just v1, Just v2) | v1 == v2                         -> chrMatchSuccess
                                 | how == CHRMatchHow_Check         -> varContinue
                                                                         (varContinue (waitv v1 >> waitv v2) (ok t1) v2)
                                                                         (\t1 -> varContinue (waitt t1 >> waitv v2) (ok t1) v2)
                                                                         v1
                                 where waitv v = unless (chrmatchenvMetaMayBind menv v) $ chrMatchWait v
                                       waitt = maybe (return ()) waitv . varTermMbKey
              (Just v1, _      ) | how == CHRMatchHow_Check         -> varContinue (if maybind then chrMatchFail else chrMatchWait v1) (flip ok t2) v1
                                 | how >= CHRMatchHow_Match && maybind
                                                                    -> varContinue (chrMatchBind v1 t2) (flip ok t2) v1
                                 | otherwise                        -> varContinue chrMatchFail (flip ok t2) v1
                                 where maybind = chrmatchenvMetaMayBind menv v1
              (_      , Just v2) | how == CHRMatchHow_Check         -> varContinue (if maybind then chrMatchFail else chrMatchWait v2) (ok t1) v2
                                 | how == CHRMatchHow_MatchAndWait  -> varContinue (chrMatchWait v2) (ok t1) v2
                                 | how == CHRMatchHow_Unify && maybind
                                                                    -> varContinue (chrMatchBind v2 t1) (ok t1) v2
                                 | otherwise                        -> varContinue chrMatchFail (ok t1) v2
                                 where maybind = chrmatchenvMetaMayBind menv v2
              _                                                     -> chrMatchFail -- ok t1 t2
        varContinue = Lk.lookupResolveAndContinueM varTermMbKey chrMatchSubst

-------------------------------------------------------------------------------------------
--- CHRCheckable
-------------------------------------------------------------------------------------------

-- | A Checkable participates in the reduction process as a guard, to be checked.
-- Checking is allowed to find/return substitutions for meta variables (not for global variables).
class (CHREmptySubstitution subst, LookupApply subst subst) => CHRCheckable env x subst where
  chrCheck :: env -> subst -> x -> Maybe subst
  chrCheck e s x = chrmatcherUnlift (chrCheckM e x) emptyCHRMatchEnv s

  chrCheckM :: env -> x -> CHRMatcher subst ()
  chrCheckM e x = chrmatcherLift $ \sg -> chrCheck e sg x

-------------------------------------------------------------------------------------------
--- CHRPrioEvaluatable
-------------------------------------------------------------------------------------------

-- | The type of value a prio representation evaluates to, must be Ord instance
type family CHRPrioEvaluatableVal p :: *

-- | A PrioEvaluatable participates in the reduction process to indicate the rule priority, higher prio takes precedence
class (Ord (CHRPrioEvaluatableVal x), Bounded (CHRPrioEvaluatableVal x)) => CHRPrioEvaluatable env x subst | x -> env subst where
  -- | Reduce to a prio representation
  chrPrioEval :: env -> subst -> x -> CHRPrioEvaluatableVal x
  chrPrioEval _ _ _ = minBound

  -- | Compare priorities
  chrPrioCompare :: env -> (subst,x) -> (subst,x) -> Ordering
  chrPrioCompare e (s1,x1) (s2,x2) = chrPrioEval e s1 x1 `compare` chrPrioEval e s2 x2
  
  -- | Lift prio val into prio
  chrPrioLift :: CHRPrioEvaluatableVal x -> x

-------------------------------------------------------------------------------------------
--- Prio
-------------------------------------------------------------------------------------------

-- | Separate priority type, where minBound represents lowest prio, and compare sorts from high to low prio (i.e. high `compare` low == LT)
newtype Prio = Prio {unPrio :: Word32}
  deriving (Eq, Bounded, Num, Enum, Integral, Real)

instance Ord Prio where
  compare = flip compare `on` unPrio
  {-# INLINE compare #-}
  
-------------------------------------------------------------------------------------------
--- Constraint API
-------------------------------------------------------------------------------------------

-- | (Class alias) API for constraint requirements
class ( CHRMatchable env c subst
      -- , CHRBuiltinSolvable env c subst
      , VarExtractable c
      , VarUpdatable c subst
      , Typeable c
      -- , Serialize c
      -- , TTKeyable c
      , TT.TreeTrieKeyable c
      , IsConstraint c
      , Ord c
      -- , Ord (TTKey c)
      , Ord (TT.TrTrKey c)
      , PP c
      -- , PP (TTKey c)
      , PP (TT.TrTrKey c)
      ) => IsCHRConstraint env c subst

-------------------------------------------------------------------------------------------
--- Guard API
-------------------------------------------------------------------------------------------

-- | (Class alias) API for guard requirements
class ( CHRCheckable env g subst
      , VarExtractable g
      , VarUpdatable g subst
      , Typeable g
      -- , Serialize g
      , PP g
      ) => IsCHRGuard env g subst

-------------------------------------------------------------------------------------------
--- Prio API
-------------------------------------------------------------------------------------------

-- | (Class alias) API for priority requirements
class ( CHRPrioEvaluatable env p subst
      , Typeable p
      -- , Serialize p
      , PP p
      ) => IsCHRPrio env p subst

-- instance {-# OVERLAPPABLE #-} IsCHRPrio env () subst

-- | (Class alias) API for backtrack priority requirements
class ( IsCHRPrio env bp subst
      , CHRMatchable env bp subst
      , PP (CHRPrioEvaluatableVal bp)
      -- -- , Num (CHRPrioEvaluatableVal bp)
      ) => IsCHRBacktrackPrio env bp subst

-------------------------------------------------------------------------------------------
--- What a constraint must be capable of
-------------------------------------------------------------------------------------------

-- | Different ways of solving
data ConstraintSolvesVia
  = ConstraintSolvesVia_Rule        -- ^ rewrite/CHR rules apply
  | ConstraintSolvesVia_Solve       -- ^ solving involving finding of variable bindings (e.g. unification)
  | ConstraintSolvesVia_Residual    -- ^ a leftover, residue
  | ConstraintSolvesVia_Fail        -- ^ triggers explicit fail
  | ConstraintSolvesVia_Succeed     -- ^ triggers explicit succes
  deriving (Show, Enum, Eq, Ord)

instance PP ConstraintSolvesVia where
  pp = pp . show

-- | The things a constraints needs to be capable of in order to participate in solving
class IsConstraint c where
  -- | Requires solving? Or is just a residue...
  cnstrRequiresSolve :: c -> Bool
  cnstrRequiresSolve c = case cnstrSolvesVia c of
    ConstraintSolvesVia_Residual -> False
    _                            -> True
  
  cnstrSolvesVia :: c -> ConstraintSolvesVia
  cnstrSolvesVia c | cnstrRequiresSolve c = ConstraintSolvesVia_Rule
                   | otherwise            = ConstraintSolvesVia_Residual

-------------------------------------------------------------------------------------------
--- Tracing options, specific for CHR solvers
-------------------------------------------------------------------------------------------

data CHRTrOpt
  = CHRTrOpt_Lookup     -- ^ trie query
  | CHRTrOpt_Stats      -- ^ various stats
  deriving (Eq, Ord, Show)
-------------------------------------------------------------------------------------------
--- CHREmptySubstitution
-------------------------------------------------------------------------------------------

-- | Capability to yield an empty substitution.
class CHREmptySubstitution subst where
  chrEmptySubst :: subst

-------------------------------------------------------------------------------------------
--- CHRMatchable
-------------------------------------------------------------------------------------------

-- | The key of a substitution
type family CHRMatchableKey subst :: *

type instance CHRMatchableKey (StackedVarLookup subst) = CHRMatchableKey subst

-- | A Matchable participates in the reduction process as a reducable constraint.
-- Unification may be incorporated as well, allowing matching to be expressed in terms of unification.
-- This facilitates implementations of 'CHRBuiltinSolvable'.
class (CHREmptySubstitution subst, LookupApply subst subst, VarExtractable x, VarLookupKey subst ~ ExtrValVarKey x) => CHRMatchable env x subst where
  -- | One-directional (1st to 2nd 'x') unify
  chrMatchTo :: env -> subst -> x -> x -> Maybe subst
  chrMatchTo env s x1 x2 = chrUnify CHRMatchHow_Match (emptyCHRMatchEnv {chrmatchenvMetaMayBind = (`Set.member` varFreeSet x1)}) env s x1 x2
    -- where free = varFreeSet x1
  
  -- | One-directional (1st to 2nd 'x') unify
  chrUnify :: CHRMatchHow -> CHRMatchEnv (VarLookupKey subst) -> env -> subst -> x -> x -> Maybe subst
  chrUnify how menv e s x1 x2 = chrmatcherUnlift (chrUnifyM how e x1 x2) menv s
  
  -- | Match one-directional (from 1st to 2nd arg), under a subst, yielding a subst for the metavars in the 1st arg, waiting for those in the 2nd
  chrMatchToM :: env -> x -> x -> CHRMatcher subst ()
  chrMatchToM e x1 x2 = chrUnifyM CHRMatchHow_Match e x1 x2

  -- | Unify bi-directional or match one-directional (from 1st to 2nd arg), under a subst, yielding a subst for the metavars in the 1st arg, waiting for those in the 2nd
  chrUnifyM :: CHRMatchHow -> env -> x -> x -> CHRMatcher subst ()
  chrUnifyM how e x1 x2 = getl chrmatcherstateEnv >>= \menv -> chrmatcherLift $ \sg -> chrUnify how menv e sg x1 x2

  -- | Solve a constraint which is categorized as 'ConstraintSolvesVia_Solve'
  chrBuiltinSolveM :: env -> x -> CHRMatcher subst ()
  chrBuiltinSolveM e x = return () -- chrmatcherLift $ \sg -> chrBuiltinSolve e sg x

instance {-# OVERLAPPABLE #-} (CHRMatchable env x subst) => CHRMatchable env (Maybe x) subst where
  chrUnifyM how e (Just x1) (Just x2) = chrUnifyM how e x1 x2
  chrUnifyM how e  Nothing   Nothing  = chrMatchSuccess
  chrUnifyM how e _         _         = chrMatchFail

instance {-# OVERLAPPABLE #-} (CHRMatchable env x subst) => CHRMatchable env [x] subst where
  chrUnifyM how e x1 x2 | length x1 == length x2 = sequence_ $ zipWith (chrUnifyM how e) x1 x2
  chrUnifyM how e _  _                           = chrMatchFail

-------------------------------------------------------------------------------------------
--- CHRMatcher API, part I
-------------------------------------------------------------------------------------------

-- | Unlift/observe (or run) a CHRMatcher
chrmatcherUnlift :: (CHREmptySubstitution subst) => CHRMatcher subst () -> CHRMatchEnv (VarLookupKey subst) -> (subst -> Maybe subst)
chrmatcherUnlift mtch menv s = do
    (s,w) <- chrmatcherRun mtch menv s
    if Set.null w then Just s else Nothing

-- | Lift into CHRMatcher
chrmatcherLift :: (LookupApply subst subst) => (subst -> Maybe subst) -> CHRMatcher subst ()
chrmatcherLift f = do
    [sl,sg] <- fmap Lk.unlifts $ getl chrmatcherstateVarLookup -- gets (unStackedVarLookup . _chrmatcherstateVarLookup)
    maybe chrMatchFail (\snew -> chrmatcherstateVarLookup =$: (Lk.apply snew)) $ f sg

-- | Run a CHRMatcher
chrmatcherRun' :: (CHREmptySubstitution subst) => (CHRMatcherFailure -> r) -> (subst -> CHRWaitForVarSet subst -> x -> r) -> CHRMatcher subst x -> CHRMatchEnv (VarLookupKey subst) -> StackedVarLookup subst -> r
chrmatcherRun' fail succes mtch menv s = either
    fail
    ((\(x,ms) -> let (s, w, _) = unCHRMatcherState ms in succes (Lk.top s) w x))
      $ flip runStateT (mkCHRMatcherState s Set.empty menv)
      $ mtch

-- | Run a CHRMatcher
chrmatcherRun :: (CHREmptySubstitution subst) => CHRMatcher subst () -> CHRMatchEnv (VarLookupKey subst) -> subst -> Maybe (subst, CHRWaitForVarSet subst)
chrmatcherRun mtch menv s = chrmatcherRun' (const Nothing) (\s w _ -> Just (s,w)) mtch menv (Lk.push chrEmptySubst $ Lk.lifts s) -- (StackedVarLookup [chrEmptySubst,s])

-------------------------------------------------------------------------------------------
--- CHRMatcher API, part II
-------------------------------------------------------------------------------------------

chrMatchSubst :: CHRMatcher subst (StackedVarLookup subst)
chrMatchSubst = getl chrmatcherstateVarLookup
{-# INLINE chrMatchSubst #-}

chrMatchBind :: forall subst k v . (LookupApply subst subst, Lookup subst k v, k ~ VarLookupKey subst, v ~ VarLookupVal subst) => k -> v -> CHRMatcher subst ()
chrMatchBind k v = chrmatcherstateVarLookup =$: ((Lk.singleton k v :: subst) `Lk.apply`)
{-# INLINE chrMatchBind #-}

chrMatchWait :: (Ord k, k ~ VarLookupKey subst) => k -> CHRMatcher subst ()
chrMatchWait k = chrMatchModifyWait (Set.insert k)
{-# INLINE chrMatchWait #-}

chrMatchSuccess :: CHRMatcher subst ()
chrMatchSuccess = return ()
{-# INLINE chrMatchSuccess #-}

-- | Normal CHRMatcher failure
chrMatchFail :: CHRMatcher subst a
chrMatchFail = throwError CHRMatcherFailure
{-# INLINE chrMatchFail #-}

-- | CHRMatcher failure because a variable binding is missing
chrMatchFailNoBinding :: CHRMatcher subst a
chrMatchFailNoBinding = throwError CHRMatcherFailure_NoBinding
{-# INLINE chrMatchFailNoBinding #-}

chrMatchSucces :: CHRMatcher subst ()
chrMatchSucces = return ()
{-# INLINE chrMatchSucces #-}

chrMatchModifyWait :: (CHRWaitForVarSet subst -> CHRWaitForVarSet subst) -> CHRMatcher subst ()
chrMatchModifyWait f =
  -- modify (\st -> st {_chrmatcherstateWaitForVarSet = f $ _chrmatcherstateWaitForVarSet st})
  -- (chrmatcherstateWaitForVarSet =$:)
  modify (\(s,w,e) -> (s,f w,e))
{-# INLINE chrMatchModifyWait #-}

-- | Match one-directional (from 1st to 2nd arg), under a subst, yielding a subst for the metavars in the 1st arg, waiting for those in the 2nd
chrMatchAndWaitToM :: CHRMatchable env x subst => Bool -> env -> x -> x -> CHRMatcher subst ()
chrMatchAndWaitToM wait env x1 x2 = chrUnifyM (if wait then CHRMatchHow_MatchAndWait else CHRMatchHow_Match) env x1 x2

-------------------------------------------------------------------------------------------
--- CHRMatchable: instances
-------------------------------------------------------------------------------------------

-- TBD: move to other file...
instance {-# OVERLAPPABLE #-} Ord (ExtrValVarKey ()) => VarExtractable () where
  varFreeSet _ = Set.empty

instance {-# OVERLAPPABLE #-} (Ord (ExtrValVarKey ()), CHREmptySubstitution subst, LookupApply subst subst, VarLookupKey subst ~ ExtrValVarKey ()) => CHRMatchable env () subst where
  chrUnifyM _ _ _ _ = chrMatchSuccess

-------------------------------------------------------------------------------------------
--- Prio: instances
-------------------------------------------------------------------------------------------

instance Show Prio where
  show = show . unPrio

instance PP Prio where
  pp = pp . unPrio

-------------------------------------------------------------------------------------------
--- CHRPrioEvaluatable: instances
-------------------------------------------------------------------------------------------

type instance CHRPrioEvaluatableVal () = Prio

{-
instance {-# OVERLAPPABLE #-} Ord x => CHRPrioEvaluatable env x subst where
  -- chrPrioEval _ _ _ = minBound
  chrPrioCompare _ (_,x) (_,y) = compare x y
-}

{-
instance {-# OVERLAPPABLE #-} CHRPrioEvaluatable env () subst where
  chrPrioLift _ = ()
  chrPrioEval _ _ _ = minBound
  chrPrioCompare _ _ _ = EQ
-}


