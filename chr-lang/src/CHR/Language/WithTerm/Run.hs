{-# LANGUAGE ScopedTypeVariables, TypeFamilies #-}

module CHR.Language.WithTerm.Run
  ( RunOpt(..)
  , Verbosity(..)

  , runFile
  )
  where

import           Data.Maybe
import           System.IO
import           Data.Time.Clock.POSIX
import           Data.Time.Clock.System
import           Data.Time.Clock.TAI
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.State.Class
import qualified Data.Set as Set

import           CHR.Parse
import           CHR.Scan

import           CHR.Data.Substitutable
import           CHR.Pretty
import           CHR.Utils
import           CHR.Data.Lens
import qualified CHR.Data.TreeTrie                                  as TT
-- import qualified UHC.Util.CHR.Solve.TreeTrie.Internal.Shared        as TT
import qualified CHR.Data.Lookup                                    as Lk
import           CHR.Types.Rule
import           CHR.Types
import           CHR.Language.Generic.AST
import           CHR.Language.Generic.Parser
import           CHR.Solve.MonoBacktrackPrio      as MBP
import           CHR.Language.WithTerm.AST
-- import           CHR.Language.Examples.Term.Visualizer

import qualified GHC.Exts                                           as Prim

data RunOpt
  = RunOpt_DebugTrace               -- ^ include debugging trace in output
  | RunOpt_SucceedOnLeftoverWork    -- ^ left over unresolvable (non residue) work is also a successful result
  | RunOpt_SucceedOnFailedSolve     -- ^ failed solve is considered also a successful result, with the failed constraint as a residue
  | RunOpt_WriteVisualization       -- ^ write visualization (html file) to disk
  | RunOpt_Verbosity Verbosity
  deriving (Eq)

mbRunOptVerbosity :: [RunOpt] -> Maybe Verbosity
mbRunOptVerbosity []                       = Nothing
mbRunOptVerbosity (RunOpt_Verbosity v : _) = Just v
mbRunOptVerbosity (_                  : r) = mbRunOptVerbosity r

-- | Run file with options
{-# INLINEABLE runFile #-}
runFile
  :: forall proxy tm
   . ( MonoBacktrackPrio (C' tm) (G' tm) (P' tm) (P' tm) (S' tm) (E' tm) IO
     , VarUpdatable tm (S' tm)
     , TmMk tm
     , PP tm
     )
  => proxy tm
  -> [RunOpt]
  -> ([C' tm] -> SolveTrace' (C' tm) (StoredCHR (C' tm) (G' tm) (P' tm) (P' tm)) (S' tm) -> PP_Doc)
  -> FilePath
  -> IO ()
runFile _ runopts chrVisualize f = do
    -- scan, parse
    msg $ "READ " ++ f    
    mbParse <- parseFile f
    case mbParse of
      Left e -> putPPLn e
      Right (prog, query, varToNmMp) -> do
        let verbosity = maximum $ [Verbosity_Quiet] ++ maybeToList (mbRunOptVerbosity runopts) ++ (if RunOpt_DebugTrace `elem` runopts then [Verbosity_ALot] else [])
            sopts = defaultCHRSolveOpts
                      { chrslvOptSucceedOnLeftoverWork = RunOpt_SucceedOnLeftoverWork `elem` runopts
                      , chrslvOptSucceedOnFailedSolve  = RunOpt_SucceedOnFailedSolve  `elem` runopts
                      , chrslvOptGatherDebugInfo       = verbosity >= Verbosity_Debug
                      , chrslvOptGatherTraceInfo       = RunOpt_WriteVisualization `elem` runopts || verbosity >= Verbosity_ALot
                      }
            mbp :: CHRMonoBacktrackPrioT (C' tm) (G' tm) (P' tm) (P' tm) (S' tm) (E' tm) IO (SolverResult (S' tm))
            mbp = do
              -- print program
              liftIO $ putPPLn $ "Rules" >-< indent 2 (vlist $ map pp prog)
              -- liftIO $ putPPLn $ "Rule TT  keys" >-< indent 2 (vlist $ map (pp . TT.chrToKey . head . ruleHead) prog)
              -- liftIO $ putPPLn $ "Rule TT2 keys" >-< indent 2 (vlist $ map (pp . TT.toTreeTrieKey) prog)
              -- freshen query vars
              query <- slvFreshSubst Set.empty query >>= \s -> return $ s `varUpd` query
              -- print query
              liftIO $ putPPLn $ "Query" >-< indent 2 (vlist $ map pp query)
              mapM_ addRule prog
              mapM_ addConstraintAsWork query
              -- solve
              liftIO $ msg $ "SOLVE " ++ f
              r <- (Prim.inline chrSolve) sopts ()
              ppSolverResult verbosity r >>= \sr -> liftIO $ putPPLn $ "Solution" >-< indent 2 sr
              if (RunOpt_WriteVisualization `elem` runopts)
                then
                  do
                    (CHRGlobState{_chrgstTrace = trace}, _) <- get
                    time <- liftIO getPOSIXTime
                    let fileName = "visualization-" ++ show (round time) ++ ".html"
                    liftIO $ writeFile fileName (showPP $ chrVisualize query trace)
                    liftIO $ msg "VISUALIZATION"
                    liftIO $ putStrLn $ "Written visualization as " ++ fileName
                else (return ())
              return r
        tBef <- getSystemTime 
        (_,(gs,_)) <- runCHRMonoBacktrackPrioT
          (chrgstVarToNmMp ^= Lk.inverse (flip (,)) varToNmMp $ emptyCHRGlobState)
          (emptyCHRBackState {- _chrbstBacktrackPrio=0 -}) {- 0 -}
          mbp
        tAft <- getSystemTime
        let tDif = systemToTAITime tAft `diffAbsoluteTime` systemToTAITime tBef
            nSteps = gs ^. MBP.chrgstStatNrSolveSteps

        -- done
        msg $ "DONE (" ++ show tDif ++ " / " ++ show nSteps ++ " = " ++ show (tDif / fromIntegral nSteps) ++ ") " ++ f
    
  where
    msg m = putStrLn $ "---------------- " ++ m ++ " ----------------"
    -- dummy = undefined :: Rule C G P P

{-
-- | run some test programs
mainTerm = do
  forM_
      [
        "typing2"
      -- , "queens"
      -- , "leq"
      -- , "var"
      -- , "ruleprio"
      -- , "backtrack3"
      -- , "unify"
      -- , "antisym"
      ] $ \f -> do
    let f' = "test/" ++ f ++ ".chr"
    runFile
      [ RunOpt_SucceedOnLeftoverWork
      , RunOpt_DebugTrace
      ] f'
-}

{-
-}
