module UHC.Util.Debug
  ( tr, trp
  )
  where

import UHC.Util.Pretty
import UHC.Util.PrettyUtils
import Debug.Trace

-------------------------------------------------------------------------
-- Tracing
-------------------------------------------------------------------------

tr m s v = trace (m ++ show s) v
trp m s v = trace (m ++ "\n" ++ disp (m >|< ":" >#< s) 1000 "") v

