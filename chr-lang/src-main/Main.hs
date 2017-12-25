{-# LANGUAGE TemplateHaskell #-}

module Main where

import System.Environment
import System.Console.GetOpt
import System.Exit
import Control.Monad

import CHR.Data.Lens
import CHR.Language.Examples.Term.Run

-- | Immediate quit options
data ImmQuit
  = ImmQuit_Help

-- | Program options
data Opts
  = Opts
      { _optVerbosity               :: Verbosity
      , _optSucceedOnNoWorkLeft     :: Bool
      , _optSucceedOnFailedSolve    :: Bool
      , _optShowVisualization       :: Bool
      , _optImmQuit                 :: [ImmQuit]
      }

mkLabel ''Opts

defaultOpts :: Opts
defaultOpts
  = Opts
      { _optVerbosity               = Verbosity_Quiet
      , _optSucceedOnNoWorkLeft     = False
      , _optSucceedOnFailedSolve    = False
      , _optShowVisualization       = False
      , _optImmQuit                 = []
      }

-- | Options for 'getOpt'
options :: [OptDescr (Opts -> Opts)]
options =
    [ mk "v" ["verbose"] "extra output, debugging output"
         (OptArg (maybe (optVerbosity ^= Verbosity_Normal) (\l -> optVerbosity ^= toEnum (read l))) "LEVEL")
    , mk "s" ["succeed-only-without-leftover"] "succeed only if no work is left over"
         (NoArg $ optSucceedOnNoWorkLeft ^= True)
    , mk "" ["succeed-on-failed"] "failed solve is considered also a successful result, with the failed constraint as a residue"
         (NoArg $ optSucceedOnFailedSolve ^= True)
    , mk "" ["visualize"] "create visualization"
         (NoArg $ optShowVisualization ^= True)
    , mk "h" ["help"] "print this help"
         (NoArg $ optImmQuit ^$= (ImmQuit_Help :))
    ]
  where
    mk so lo desc o = Option so lo o desc

-- RunOpt_Verbosity

main = do
    args <- getArgs
    progname <- getProgName

    case getOpt Permute options args of
       -- options ok
       (o,[fn],[]) -> do
           let opts = foldl (flip id) defaultOpts o
           case _optImmQuit opts of
             imm@(_:_) -> forM_ imm $ \iq -> case iq of
               ImmQuit_Help -> printUsage progname []

             -- no immediate quit options
             _ -> do
               flip runFile fn $ 
                 [RunOpt_Verbosity $ _optVerbosity opts] ++
                 (if _optSucceedOnNoWorkLeft opts then [] else [RunOpt_SucceedOnLeftoverWork]) ++
                 (if _optShowVisualization opts then [RunOpt_WriteVisualization] else []) ++
                 (if _optSucceedOnFailedSolve opts then [RunOpt_SucceedOnFailedSolve] else [])

       (_,_,errs) -> do
           printUsage progname errs
           exitFailure

    return ()

  where
    printUsage progname errs = putStrLn $ concat errs ++ usageInfo (header progname) options
    header progname = "Usage: " ++ progname ++ " [OPTION...] file\n\nOptions:"

