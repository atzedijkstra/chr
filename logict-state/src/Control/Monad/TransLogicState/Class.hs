{-# LANGUAGE ScopedTypeVariables #-}

module Control.Monad.TransLogicState.Class
  ( TransLogicState(..)
  
  , observe
  , observeAll
  , observeMany
  )
  where

-- import Data.Typeable

import Control.Arrow
import Control.Monad.Identity
import Control.Monad.Trans

-- | Additions to MonadTrans specifically useful for LogicState
class MonadTrans t => TransLogicState s t where
  -------------------------------------------------------------------------
  -- | Extracts the first result from a 't m' computation,
  -- failing otherwise.
  observeT :: (MonadFail m) => s -> t m a -> m a
  observeT e m = fmap head $ observeManyT e 1 m
  
  -------------------------------------------------------------------------
  -- | Extracts all results from a 't m' computation.
  observeAllT :: (Monad m) => s -> t m a -> m [a]
  observeAllT e = fmap fst . observeStateAllT e
  
  -------------------------------------------------------------------------
  -- | Extracts all results from a 't m' computation.
  observeStateAllT :: (Monad m) => s -> t m a -> m ([a],s)
  observeStateAllT e = observeStateManyT e maxBound
  
  -------------------------------------------------------------------------
  -- | Extracts up to a given number of results from a 't m' computation.
  observeManyT :: forall m a . (Monad m) => s -> Int -> t m a -> m [a]
  observeManyT e n m = fmap fst $ observeStateManyT e n m

  -------------------------------------------------------------------------
  -- | Extracts up to a given number of results from a 't m' computation.
  observeStateManyT :: forall m a . (Monad m) => s -> Int -> t m a -> m ([a],s)
  observeStateManyT e n m = fmap (first $ take n) $ observeStateAllT e m

  -- | Lift a monad by threading the state available in the transformed monad through it
  liftWithState :: Monad m => (s -> m (a,s)) -> t m a

-------------------------------------------------------------------------
-- | Extracts the first result from a LogicVar computation.
observe :: (TransLogicState s t) => s -> t Maybe a -> Maybe a
observe e = observeT e

-------------------------------------------------------------------------
-- | Extracts all results from a LogicVar computation.
observeAll :: (TransLogicState s t) => s -> t Identity a -> [a]
observeAll e = runIdentity . observeAllT e

-------------------------------------------------------------------------
-- | Extracts up to a given number of results from a LogicVar computation.
observeMany :: (TransLogicState s t) => s -> Int -> t Identity a -> [a]
observeMany e i = runIdentity . observeManyT e i

