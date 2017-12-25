{-# LANGUAGE DeriveFunctor, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}

-------------------------------------------------------------------------------------------
-- | Lookups combined into stack of lookups, allowing combined lookup coupled with updates on top of stack only
-------------------------------------------------------------------------------------------

module CHR.Data.Lookup.Stacked
  ( Stacked(..)
  , StackedElt
  
  , Stacks(..)
  )
  where

-------------------------------------------------------------------------------------------
import           Control.Applicative
import           Control.Arrow
import           Control.Monad.State
import           CHR.Data.Lookup.Types
import           CHR.Pretty
import           CHR.Data.Lens               as L
import           Prelude                     hiding (lookup, null, map)
import           Data.Maybe
import qualified Data.List                   as List
import qualified Data.Map                    as Map
import qualified Data.Set                    as Set
import qualified Data.Vector.Unboxed         as UV
import qualified Data.Vector.Unboxed.Mutable as MV
-------------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------------------

-- | Stacked Lookup derived from a base one, to allow a use of multiple lookups but update on top only
newtype Stacks l = Stacks {unStacks :: [l]}
  deriving (Functor, Applicative)

-------------------------------------------------------------------------------------------
-- Lenses
-------------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------------
-- Stacked API
-------------------------------------------------------------------------------------------

type family StackedElt stk :: *

-- | Functionality on top of 'Lookup' for awareness of a scope.
-- Minimal definition 'lifts', 'unlifts,', 'top'/'topM', 'pop'/'popM', 'push'/'pushM'
class Stacked stk where
  -- lifting in/out
  lifts         :: StackedElt stk -> stk
  unlifts       :: stk -> [StackedElt stk]
  
  -- basic api
  top           :: stk -> StackedElt stk
  pop           :: stk -> (StackedElt stk,stk)
  push          :: StackedElt stk -> stk -> stk
  
  -- monadic api
  topM          :: (MonadState stk m) => m (StackedElt stk)
  popM          :: (MonadState stk m) => m (StackedElt stk)
  pushM         :: (MonadState stk m) => StackedElt stk -> m ()
  
  -- lifted variations
  tops          :: stk -> stk
  pops          :: stk -> (stk,stk)
  pushs         :: stk -> stk -> stk        -- ^ push, but only top of first arg

  -- lifted monadic variations
  topsM         :: (MonadState stk m) => m stk
  popsM         :: (MonadState stk m) => m stk
  pushsM        :: (MonadState stk m) => stk -> m ()

  -- defaults one way
  tops      = lifts . top
  pops      = first lifts . pop
  pushs     = push . top
  topsM     = gets tops
  popsM     = state pops
  pushsM    = modify . pushs
  
  -- defaults both ways
  topM = gets top
  top  = evalState topM
  
  popM = state pop
  pop  = runState popM

  pushM = modify . push
  push  = execState . pushM

-------------------------------------------------------------------------------------------
-- Default impl
-------------------------------------------------------------------------------------------

type instance StackedElt (Stacks e) = e

instance Stacked (Stacks lkup) where
  lifts e = Stacks [e]
  unlifts = unStacks
  top = List.head . unStacks
  pop (Stacks (h:t)) = (h, Stacks t)
  push h (Stacks t) = Stacks (h:t)

instance (Lookup lkup k v) => Lookup (Stacks lkup) k v where
  lookup  k  = listToMaybe . catMaybes . List.map (lookup k) . unStacks
  alter f k  = Stacks . List.map (alter f k) . unStacks
  null       = all null . unStacks
  toList     = concatMap toList . unStacks
  fromList   = lifts . fromList

  -- for performance reasons
  keysSet = Set.unions . List.map keysSet . unStacks

-- modifications only for top level, otherwise use <$>
instance LookupApply l1 l2 => LookupApply l1 (Stacks l2) where
  l1 `apply` Stacks (h:t) = Stacks $ apply l1 h : t

instance Show (Stacks s) where
  show _ = "Stacks"

instance PP s => PP (Stacks s) where
  pp (Stacks xs) = ppCurlysCommas $ List.map pp xs

