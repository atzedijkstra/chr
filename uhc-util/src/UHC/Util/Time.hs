-- wrapping around time to look like old-time, only for that what is being used.

module UHC.Util.Time
  ( module Data.Time.Compat,
    module Data.Time,
    module Data.Time.Clock,
    ClockTime,
    diffClockTimes,
    noTimeDiff,
    getClockTime
  )
  where

import Data.Time
import Data.Time.Clock
import Data.Time.Compat

-- | a for now alias for old-time ClockTime
type ClockTime = UTCTime

diffClockTimes = diffUTCTime

noTimeDiff :: NominalDiffTime
noTimeDiff = toEnum 0

getClockTime :: IO ClockTime
getClockTime = getCurrentTime

