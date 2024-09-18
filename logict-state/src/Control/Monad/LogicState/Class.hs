{-# LANGUAGE FunctionalDependencies #-}

module Control.Monad.LogicState.Class
  ( MonadLogicState(..)
  )
  where

import Control.Monad
import Control.Monad.Logic.Class (MonadLogic)
import Control.Monad.State (MonadState)

-------------------------------------------------------------------------------
-- | API for MonadLogic which allows state and backtracking on it.
class (MonadLogic m, Monad ms, MonadState (f gs bs) m) => MonadLogicState f gs bs ms m | m -> ms where
    
    -- | Return argument monad with the current backtrackable part of the state remembered.
    -- If the default def is not overridden this a no-op.
    -- This function complements 'mplus' for 'LogicT', 'mplus' backtracks on results, not on state, which is what this function should do.
    -- 'roll' accepts the end state of the backtrack attempt resp the state to backtrack to, returns to state to backtrack to.
    backtrackWithRoll
      :: (gs -> bs -> bs -> ms bs) -- ^ roll
      -> m a
      -> m (m a)
    backtrackWithRoll _ = backtrack
    
    -- | special case of 'backtrackWith'
    backtrack :: m a -> m (m a)
    backtrack = backtrackWithRoll (\_ _ bs -> return bs)
    
    

