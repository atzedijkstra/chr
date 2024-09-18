{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies, UndecidableInstances, ExistentialQuantification, ScopedTypeVariables, StandaloneDeriving, GeneralizedNewtypeDeriving, TemplateHaskell, NoMonomorphismRestriction #-}

-------------------------------------------------------------------------------------------
--- Constraint Handling Rules
-------------------------------------------------------------------------------------------

{- |
Derived from work by Gerrit vd Geest, but with searching structures for predicates
to avoid explosion of search space during resolution.
-}

module UHC.Util.CHR.Base
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
import           UHC.Util.VarMp
import           UHC.Util.Lookup            (Lookup, Stacked, LookupApply)
import qualified UHC.Util.Lookup            as Lk
import qualified UHC.Util.Lookup.Stacked    as Lk
import           Data.Word
import           Data.Monoid
import           Data.Typeable
import           Data.Function
import           Unsafe.Coerce
import qualified Data.Set as Set
import           UHC.Util.Pretty
import           UHC.Util.CHR.Key
import           Control.Monad
import           Control.Monad.State.Strict
import           Control.Monad.Except
import           Control.Monad.Identity
import           UHC.Util.Lens
import           UHC.Util.Utils
import           UHC.Util.Binary
import           UHC.Util.Serialize
import           UHC.Util.Substitutable

import           CHR.Types.Core             hiding
                                            ( IsCHRConstraint
                                            , IsCHRGuard
                                            , IsCHRBacktrackPrio
                                            , IsCHRPrio
                                            )
import qualified CHR.Types.Core             as CHR

import           UHC.Util.Debug


-------------------------------------------------------------------------------------------
--- Constraint API
-------------------------------------------------------------------------------------------

-- | (Class alias) API for constraint requirements
class ( CHRMatchable env c subst
      -- , CHRBuiltinSolvable env c subst
      , VarExtractable c
      , VarUpdatable c subst
      , Typeable c
      , Serialize c
      , TTKeyable c
      , IsConstraint c
      , Ord c
      , Ord (TTKey c)
      , PP c
      , PP (TTKey c)
      ) => IsCHRConstraint env c subst

-------------------------------------------------------------------------------------------
--- Guard API
-------------------------------------------------------------------------------------------

-- | (Class alias) API for guard requirements
class ( CHRCheckable env g subst
      , VarExtractable g
      , VarUpdatable g subst
      , Typeable g
      , Serialize g
      , PP g
      ) => IsCHRGuard env g subst

-------------------------------------------------------------------------------------------
--- Prio API
-------------------------------------------------------------------------------------------

-- | (Class alias) API for priority requirements
class ( CHRPrioEvaluatable env p subst
      , Typeable p
      , Serialize p
      , PP p
      ) => IsCHRPrio env p subst

-- instance {-# OVERLAPPABLE #-} IsCHRPrio env () subst

-- | (Class alias) API for backtrack priority requirements
class ( IsCHRPrio env bp subst
      , CHRMatchable env bp subst
      , PP (CHRPrioEvaluatableVal bp)
      -- , Num (CHRPrioEvaluatableVal bp)
      ) => IsCHRBacktrackPrio env bp subst


