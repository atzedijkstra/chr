{-# LANGUAGE UndecidableInstances, Rank2Types, FlexibleInstances, FlexibleContexts, GADTs, ScopedTypeVariables, FunctionalDependencies #-}

-------------------------------------------------------------------------
-- |
-- Module      : Control.Monad.LogicState
-- Copyright   : (c) Atze Dijkstra
-- License     : BSD3
--
-- Maintainer  : atzedijkstra@gmail.com
-- Stability   : experimental, (as of 20160218) under development
-- Portability : non-portable
--
-- A backtracking, logic programming monad partially derived and on top of logict, adding backtrackable state.
--
--    LogicT (and thus this library as well) is adapted from the paper
--    /Backtracking, Interleaving, and Terminating
--        Monad Transformers/, by
--    Oleg Kiselyov, Chung-chieh Shan, Daniel P. Friedman, Amr Sabry
--    (<http://www.cs.rutgers.edu/~ccshan/logicprog/LogicT-icfp2005.pdf>).
--
-- 
-------------------------------------------------------------------------

module Control.Monad.LogicState (
    module Control.Monad.Logic.Class,
    module Control.Monad,
    module Control.Monad.Trans,
    module Control.Monad.LogicState.Class,
    module Control.Monad.TransLogicState.Class,
    -- * The LogicState monad
    LogicState,
    LogicStateT(..),
  ) where

import Data.Maybe
import Data.Typeable

import Control.Applicative

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans

import Control.Monad.State
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.Error.Class

import Data.Monoid (Monoid(mappend, mempty))
import qualified Data.Foldable as F
import qualified Data.Traversable as T

import Control.Monad.Logic.Class

import Control.Monad.LogicState.Class
import Control.Monad.TransLogicState.Class

-------------------------------------------------------------------------
-- | A monad transformer for performing backtracking computations
-- layered over another monad 'm', with propagation of global and backtracking state, e.g. resp. for freshness/uniqueness and maintaining variable mappings.
newtype LogicStateT gs bs m a =
    LogicStateT { unLogicStateT ::
      forall r. LogicContS gs bs r m a
    }

-- | Convenience types
type LogicStateS gs bs r m = StateT (gs,bs) m r -- (gs,bs) -> m (r,(gs,bs))
type LogicContS gs bs r m a =
           (   a                                 --  result
            -> LogicStateS gs bs r m             --  failure continuation
            -> LogicStateS gs bs r m
           )                                     -- ^ success continuation
        -> LogicStateS gs bs r m                 -- ^ failure continuation
        -> LogicStateS gs bs r m                 -- ^ global + backtracking state

instance Functor (LogicStateT gs bs f) where
    fmap f lt = LogicStateT $ \sk -> unLogicStateT lt (sk . f)

instance Applicative (LogicStateT gs bs f) where
    pure a = LogicStateT ($ a)
    f <*> a = LogicStateT $ \sk -> unLogicStateT f (\g -> unLogicStateT a (sk . g))

instance Monad (LogicStateT gs bs m) where
    return = pure
    m >>= f = LogicStateT $ \sk -> unLogicStateT m (\a -> unLogicStateT (f a) sk)

instance MonadFail (LogicStateT gs bs m) where
    fail _ = LogicStateT $ flip const

instance Alternative (LogicStateT gs bs f) where
    empty = LogicStateT $ flip const
    -- state backtracking variant, but in general interacts badly with other combinators using msplit. Backtracking separately available.
    -- f1 <|> f2 = LogicStateT $ \sk fk -> StateT $ \s@(_,bs) -> runStateT (unLogicStateT f1 sk (StateT $ \(gs',_) -> runStateT (unLogicStateT f2 sk fk) (gs',bs))) s
    f1 <|> f2 = LogicStateT $ \sk fk -> unLogicStateT f1 sk (unLogicStateT f2 sk fk)

instance MonadPlus (LogicStateT gs bs m) where
  mzero = empty
  {-# INLINE mzero #-}
  mplus = (<|>)
  {-# INLINE mplus #-}

instance MonadTrans (LogicStateT gs bs) where
    lift m = LogicStateT $ \sk fk -> StateT $ \s -> m >>= \a -> runStateT (sk a fk) s

instance (MonadIO m) => MonadIO (LogicStateT gs bs m) where
    liftIO = lift . liftIO

instance MonadReader r m => MonadReader r (LogicStateT gs bs m) where
    ask = lift ask
    local f m = LogicStateT $ \sk fk -> StateT $ runStateT $ unLogicStateT m (\a fk -> StateT $ local f . runStateT (sk a fk)) (StateT $ local f . runStateT fk)

instance (Monad m) => MonadLogic (LogicStateT gs bs m) where
    msplit m =
       liftWithState $ runStateT $ unLogicStateT m
         (\a fk -> return (Just (a, liftWithState (runStateT fk) >>= reflect)))
         (return Nothing)

instance TransLogicState (gs,bs) (LogicStateT gs bs) where
  -- observe s lt = runIdentity $ evalStateT (unLogicStateT lt (\a _ -> return a) (error "No answer.")) s

  observeT s lt = evalStateT (unLogicStateT lt (\a _ -> return a) (fail "No answer.")) s
    
  observeStateAllT s m = runStateT (unLogicStateT m
    (\a fk -> fk >>= \as -> return (a:as))
    (return []))
    s

  observeStateManyT s n m = runStateT (obs n m) s
   where
     obs n m
        | n <= 0 = return []
        | n == 1 = unLogicStateT m (\a _ -> return [a]) (return [])
        | otherwise = unLogicStateT (msplit m) sk (return [])
     
     sk Nothing _ = return []
     sk (Just (a, m')) _ = StateT $ \s -> (\as -> (a:as,s)) `liftM` observeManyT s (n-1) m'

  liftWithState m = LogicStateT $ \sk fk -> StateT $ \s -> m s >>= \(a,s) -> runStateT (sk a fk) s
  {-# INLINE liftWithState #-}

instance Monad m => MonadState (gs,bs) (LogicStateT gs bs m) where
    get   = LogicStateT $ \sk fk -> get >>= \s -> sk s fk
    put s = LogicStateT $ \sk fk -> put s >>= \a -> sk a fk

instance (Monad m) => MonadLogicState (,) gs bs m (LogicStateT gs bs m) where
    backtrackWithRoll roll m = do
      (_,bs1) <- get
      return $ LogicStateT $ \sk fk ->
        StateT $ \(gs2,bs2) -> do
          bs <- roll gs2 bs2 bs1
          runStateT (unLogicStateT m sk fk) (gs2,bs)


-------------------------------------------------------------------------
-- | The basic LogicVar monad, for performing backtracking computations
-- returning values of type 'a'
type LogicState gs bs = LogicStateT gs bs Identity

