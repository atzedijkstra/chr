module CHR.Language.Examples.Term.Run
  ( Run.RunOpt(..)
  , Run.Verbosity(..)

  , runFile
  )
  where

import           Data.Proxy
import           CHR.Language.Examples.Term.AST
import           CHR.Language.Examples.Term.Visualizer

import qualified CHR.Language.WithTerm.Run                          as Run

import qualified GHC.Exts                                           as Prim

-- | Run file with options
runFile :: [Run.RunOpt] -> FilePath -> IO ()
runFile runopts f = (Prim.inline Run.runFile) (Proxy :: Proxy Tm) runopts chrVisualize f
