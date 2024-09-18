{-| Wrapper around 'Control.Monad.Logic'
-}

module Control.Monad.LogicState.Logic
  ( module Control.Monad.Logic
  , module Control.Monad.TransLogicState.Class
  )
  where

import           Control.Monad.Logic hiding (observeT, observeAllT, observeManyT, observe, observeAll, observeMany)
import qualified Control.Monad.Logic as CML
import           Control.Monad.Trans.Class (lift)

import           Control.Monad.TransLogicState.Class

instance TransLogicState () LogicT where
  observeT _ = CML.observeT
  observeAllT _ = CML.observeAllT
  observeManyT _ = CML.observeManyT
  liftWithState m = lift $ m () >>= (return . fst)
  
