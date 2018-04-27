{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, UndecidableInstances, NoMonomorphismRestriction, MultiParamTypeClasses #-}

-------------------------------------------------------------------------------------------
-- | CHR TreeTrie based solver shared internals, for all solvers
-------------------------------------------------------------------------------------------

module CHR.Types
  ( module CHR.Types.Core
  , module CHR.Data.TreeTrie
  
  , CHRKey

  , WorkTime
  , initWorkTime

  , Work'(..)
  , Work

  , SolveStep'(..)
  , SolveTrace'
  , emptySolveTrace
  , ppSolveTrace
  )
  where

import qualified CHR.Data.TreeTrie          as TT
import           CHR.Data.TreeTrie          ( TrTrKey )
import           CHR.Pretty                 as Pretty
import           CHR.Data.AssocL
import           CHR.Types.Core             ( IVar
                                            , NmToVarMp, emptyNmToVarMp
                                            , Prio
                                            , CHRPrioEvaluatableVal
                                            , IsConstraint
                                            , IsCHRGuard
                                            , IsCHRConstraint
                                            , IsCHRPrio
                                            , IsCHRBacktrackPrio
                                            , CHRCheckable
                                            , CHRMatchable
                                            , CHRPrioEvaluatable
                                            , CHREmptySubstitution
                                            , CHRMatcher
                                            , CHRMatchableKey
                                            , CHRMatcherFailure
                                            )

import qualified Data.Map                   as Map

-------------------------------------------------------------------------------------------
--- CHR key
-------------------------------------------------------------------------------------------

-- | Convenience alias for key into CHR store
type CHRKey v = TT.Key (TT.TrTrKey v)

-------------------------------------------------------------------------------------------
--- WorkTime, the time/history counter for solver work
-------------------------------------------------------------------------------------------

-- | All solver constraints are identified individually with a timestamp, also serving as its identification depending on the solver
type WorkTime = Int

initWorkTime :: WorkTime
initWorkTime = 0

-------------------------------------------------------------------------------------------
--- Solver work and/or residual (non)work
-------------------------------------------------------------------------------------------

type WorkKey      v = CHRKey v

-- | A chunk of work to do when solving, a constraint + sequence nr
data Work' k c
  = Work
      { workKey     :: k                            -- ^ the key into the CHR store
      , workCnstr   :: !c                           -- ^ the constraint to be reduced
      , workTime    :: WorkTime                     -- ^ the timestamp identification at which the work was added
      }
  | Work_Residue
      { workCnstr   :: !c                           -- ^ the residual constraint
      }
  | Work_Solve
      { workCnstr   :: !c                           -- ^ constraint which must be solved
      }
  | Work_Fail

type Work c = Work' (WorkKey c) c

type instance TT.TrTrKey (Work' k c) = TT.TrTrKey c

instance Show (Work' k c) where
  show _ = "SolveWork"

instance (PP k, PP c) => PP (Work' k c) where
  pp (Work {workKey=k, workCnstr=c, workTime=t})
                          = ppParens k >|< "@" >|< t >#< c
  pp (Work_Residue   c  ) = pp                           c
  pp (Work_Solve     c  ) = pp                           c
  pp (Work_Fail         ) = pp "fail"

-------------------------------------------------------------------------------------------
--- Solver trace
-------------------------------------------------------------------------------------------

-- | A trace step
data SolveStep' c r s
  = SolveStep
      { stepChr         :: r
      , stepSubst       :: s
      , stepAlt         :: Maybe [c]
      , stepNewTodo     :: [c]
      , stepNewDone     :: [c]
      }
  | SolveStats
      { stepStats       :: Map.Map String PP_Doc
      }
  | SolveDbg
      { stepPP          :: PP_Doc
      }

type SolveTrace' c r s = [SolveStep' c r s]

emptySolveTrace :: SolveTrace' c r s
emptySolveTrace = []

instance Show (SolveStep' c r s) where
  show _ = "SolveStep"

instance (PP r, PP c) => {- (PP c, PP g) => -} PP (SolveStep' c r s) where
  pp (SolveStep   step _ _ todo done) = "STEP" >#< (step >-< "new todo:" >#< ppBracketsCommas todo >-< "new done:" >#< ppBracketsCommas done)
  pp (SolveStats  stats             ) = "STATS"  >#< (ppAssocLV (Map.toList stats))
  pp (SolveDbg    p                 ) = "DBG"  >#< p

ppSolveTrace :: (PP r, PP c) => {- (PP s, PP c, PP g) => -} SolveTrace' c r s -> PP_Doc
ppSolveTrace tr = ppBracketsCommasBlock [ pp st | st <- tr ]
