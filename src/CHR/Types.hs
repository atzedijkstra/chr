{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, UndecidableInstances, NoMonomorphismRestriction, MultiParamTypeClasses #-}

-------------------------------------------------------------------------------------------
-- | CHR TreeTrie based solver shared internals, for all solvers
-------------------------------------------------------------------------------------------

module CHR.Types
  -- ( CHRTrie'
  -- , CHRTrieKey
-- 
  -- , chrToKey
  -- , chrToWorkKey
-- 
  -- , CHRKey
  -- , CHRKey2
-- 
  -- , WorkTime
  -- , initWorkTime
  -- 
  -- , WorkKey
  -- , WorkKey2
  -- , Work'(..)
  -- , Work
  -- , Work2
  -- 
  -- , SolveStep'(..)
  -- , SolveTrace'
  -- , emptySolveTrace
  -- -- , ppSolveTrace
  -- 
  -- )
  where

-- import           CHR.Data.CHR.Key
import qualified CHR.Data.TreeTrie          as TT2
import           CHR.Types.Rule             (Rule)
import           CHR.Types.Core             ()

-- import           UHC.Util.Pretty            as Pretty
-- import           UHC.Util.AssocL

import qualified Data.Map                   as Map

-------------------------------------------------------------------------------------------
--- Choice of Trie structure
-------------------------------------------------------------------------------------------

-- type CHRTrie'  k v = TreeTrie.TreeTrie  (TTKey k) v
-- -- type CHRTrie2' k v = TreeTrie2.TreeTrie (TreeTrie2.TrTrKey k) v
-- type CHRTrieKey  v = TreeTrie.TreeTrieKey  (TTKey v)
-- -- type CHRTrieKey2 v = TreeTrie2.TreeTrieKey (TTKey v)

-- -- | Obtain key for use in rule
-- chrToKey :: (TTKeyable x, TrTrKey x ~ TTKey x) => x -> CHRTrieKey x
-- chrToKey = ttkFixate . toTTKey
-- {-# INLINE chrToKey #-}

{-
-- | Obtain key for use in rule
chrToKey2 :: (TT2.TreeTrieKeyable x) => x -> TT2.Key (TT2.TrTrKey x)
chrToKey2 = toTreeTrieKey
{-# INLINE chrToKey2 #-}
-}

-- -- | Obtain key for use in to be solved context (i.e. work)
-- chrToWorkKey :: (TTKeyable x) => x -> CHRTrieKey x
-- chrToWorkKey = ttkFixate . toTTKey' (defaultTTKeyableOpts {ttkoptsVarsAsWild = False})
-- {-# INLINE chrToWorkKey #-}

-------------------------------------------------------------------------------------------
--- CHR key
-------------------------------------------------------------------------------------------

-- | Convenience alias for key into CHR store
-- type CHRKey  v = CHRTrieKey v
type CHRKey2 v = TT2.Key (TT2.TrTrKey v)

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

-- type WorkKey       v = CHRKey  v
type WorkKey2      v = CHRKey2 v

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

-- type Work  c = Work' (WorkKey  c) c
type Work2 c = Work' (WorkKey2 c) c

-- type instance TTKey       (Work' k c) = TTKey       c
type instance TT2.TrTrKey (Work' k c) = TT2.TrTrKey c

instance Show (Work' k c) where
  show _ = "SolveWork"

{-
instance (PP k, PP c) => PP (Work' k c) where
  pp (Work {workKey=k, workCnstr=c, workTime=t})
                          = ppParens k >|< "@" >|< t >#< c
  pp (Work_Residue   c  ) = pp                           c
  pp (Work_Solve     c  ) = pp                           c
  pp (Work_Fail         ) = pp "fail"
-}

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
  -- | SolveStats
  --     { stepStats       :: Map.Map String PP_Doc
  --     }
  -- | SolveDbg
  --     { stepPP          :: PP_Doc
  --     }

type SolveTrace' c r s = [SolveStep' c r s]

emptySolveTrace :: SolveTrace' c r s
emptySolveTrace = []

instance Show (SolveStep' c r s) where
  show _ = "SolveStep"

{-
instance (PP r, PP c) => {- (PP c, PP g) => -} PP (SolveStep' c r s) where
  pp (SolveStep   step _ _ todo done) = "STEP" >#< (step >-< "new todo:" >#< ppBracketsCommas todo >-< "new done:" >#< ppBracketsCommas done)
  pp (SolveStats  stats             ) = "STATS"  >#< (ppAssocLV (Map.toList stats))
  pp (SolveDbg    p                 ) = "DBG"  >#< p

ppSolveTrace :: (PP r, PP c) => {- (PP s, PP c, PP g) => -} SolveTrace' c r s -> PP_Doc
ppSolveTrace tr = ppBracketsCommasBlock [ pp st | st <- tr ]
-}
