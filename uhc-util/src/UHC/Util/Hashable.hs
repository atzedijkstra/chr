{-| Re-export of hashable package,
    in addition providing some of the instances for datatypes defined in the remainder of the uhc-util package.
-}

module UHC.Util.Hashable
  ( module Data.Hashable
  )
  where

import           Data.Hashable
import qualified Data.Map as Map
import qualified Data.Set as Set
import           UHC.Util.FPath

-- Instances

instance Hashable FPath

-- instance Hashable a => Hashable (Set.Set a) where
--   hashWithSalt = Set.foldl' hashWithSalt

-- instance (Hashable a, Hashable b) => Hashable (Map.Map a b) where
--   hashWithSalt = Map.foldlWithKey (\salt a b -> salt `hashWithSalt` a `hashWithSalt` b)
