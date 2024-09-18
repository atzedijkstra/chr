
-------------------------------------------------------------------------
-- Wrapper module around pretty printing
-------------------------------------------------------------------------

module UHC.Util.Pretty
  ( module CHR.Pretty

  , putPPFPath
  )
  where

import CHR.Pretty
import UHC.Util.FPath
import UHC.Util.Time
import System.IO


-------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------


instance PP FPath where
  pp = pp . fpathToStr


instance PP ClockTime where
  pp = pp . show

-------------------------------------------------------------------------
-- PP printing to file
-------------------------------------------------------------------------



putPPFPath :: FPath -> PP_Doc -> Int -> IO ()
putPPFPath fp pp wid
  = do { fpathEnsureExists fp
       ; putPPFile (fpathToStr fp) pp wid
       }

