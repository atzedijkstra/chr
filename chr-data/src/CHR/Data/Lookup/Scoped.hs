{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}

-------------------------------------------------------------------------------------------
-- | Scoped Lookup allowing items to have a scope associated. A scope identifies a position in a tree representing nesting.
-- The Lookup has its own scope, i.e. maintains contextual state about 'where it is' in terms of nesting, thus allowing to query whether an item can see the current scope.
-------------------------------------------------------------------------------------------

module CHR.Data.Lookup.Scoped
  ( Scoped(..)
  
  , DefaultScpsLkup
  , defaultScpsLkup
  )
  where

-------------------------------------------------------------------------------------------
import           Control.Arrow
import           Control.Monad.State
import           CHR.Data.Lookup.Types       hiding (empty)
import qualified CHR.Data.Lookup.Types       as Lkup
import           CHR.Pretty             hiding (empty)
import           CHR.Data.Lens               as L
import           Prelude                     hiding (lookup, null, map)
import qualified Data.List                   as List
import qualified Data.Map                    as Map
import qualified Data.Vector.Unboxed         as UV
import qualified Data.Vector.Unboxed.Mutable as MV
-------------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------------------

-- | Scope id
type ScpId = Int

-- | Scopes
data Scopes
  = Scopes
      { _scopesVec     :: UV.Vector ScpId
      , _scopesFree    :: ScpId
      , _scopesCur     :: ScpId
      }

instance Show Scopes where
  show (Scopes v _ _) = show v

instance PP Scopes where
  pp = pp . show

-- | Scoped item
data ScopedItem v
  = ScopedItem
      { _scopeditemId  :: ScpId
      , _scopeditemVal :: v
      }
  deriving Show

instance PP v => PP (ScopedItem v) where
  pp (ScopedItem i v) = v >|< ppParens i

-- | Default scope lookup
data ScpsLkup lkup scps
  = ScpsLkup
      { _scpslkupBase    :: lkup
      , _scpslkupScopes  :: scps
      }
  deriving Show

instance (PP lkup, PP scps) => PP (ScpsLkup lkup scps) where
  pp (ScpsLkup lkup scps) = lkup >-< scps

-------------------------------------------------------------------------------------------
-- Lenses
-------------------------------------------------------------------------------------------

mkLabel ''ScopedItem
mkLabel ''Scopes
mkLabel ''ScpsLkup

-------------------------------------------------------------------------------------------
-- Scopes utils
-------------------------------------------------------------------------------------------

-- | Ensure enough free slots
scpEnsure :: Int -> Scopes -> Scopes
scpEnsure free s@(Scopes {_scopesVec=v, _scopesFree=f})
  | free >= f - UV.length v = s
  | otherwise               = s {_scopesVec = v UV.++ UV.replicate (free `max` ((3 * UV.length v) `div` 2)) 0}
{-# INLINE scpEnsure #-}

-- | Allocate new entry, init to point back to current, switch to it; assume enough free size.
-- Modification is done destructively but only on newly allocated position
scpAlloc :: Scopes -> (ScpId, Scopes)
scpAlloc s@(Scopes {_scopesVec=v, _scopesFree=f, _scopesCur=c}) = (f, s {_scopesFree = f+1, _scopesVec = UV.modify (\v -> MV.write v f c) v, _scopesCur = f})
{-# INLINE scpAlloc #-}

-------------------------------------------------------------------------------------------
-- Scope API
-------------------------------------------------------------------------------------------

-- | Functionality on top of 'Lookup' for awareness of a scope
class Scoped c where
  empty         :: c
  new           :: c -> (ScpId,c)
  pop           :: c -> (ScpId,c)
  switch        :: ScpId -> c -> (ScpId,c)
  scope         :: c -> ScpId
  -- | Something at current scope is visible from given scope, i.e. given scope is inside current scope
  curIsVisibleFrom  :: ScpId -> c -> Bool
  
  -- monadic api
  newM          :: (MonadState c m) => m ScpId
  popM          :: (MonadState c m) => m ScpId
  switchM       :: (MonadState c m) => ScpId -> m ScpId
  scopeM        :: (MonadState c m) => m ScpId
  curIsVisibleFromM :: (MonadState c m) => ScpId -> m Bool
  
  -- defaults both ways
  newM = state new
  new  = runState newM
  
  popM = state pop
  pop  = runState popM

  switchM = state . switch
  switch  = runState . switchM
  
  scopeM = gets scope
  scope  = evalState scopeM
  
  curIsVisibleFromM = gets . curIsVisibleFrom
  curIsVisibleFrom  = evalState . curIsVisibleFromM

instance Scoped Scopes where
  empty  = Scopes (UV.replicate 3 0) 1 0
  new    = scpAlloc . scpEnsure 1
  switch i s = (_scopesCur s, s {_scopesCur = i})
  scope  = _scopesCur
  pop s@(Scopes {_scopesVec=v, _scopesCur=c})
         = (c, s {_scopesCur = v UV.! c})
  curIsVisibleFrom i s@(Scopes {_scopesVec=v, _scopesCur=c})
    | i == c    = True
    | i == 0    = False
    | otherwise = curIsVisibleFrom (v UV.! i) s

-------------------------------------------------------------------------------------------
-- Default impl
-------------------------------------------------------------------------------------------

type DefaultScpsLkup k v = ScpsLkup (Map.Map k (ScopedItem v)) Scopes

defaultScpsLkup :: DefaultScpsLkup k v
defaultScpsLkup = ScpsLkup Map.empty empty

whenInScps :: Scoped c => c -> ScpId -> v -> Maybe v
whenInScps scps sc v = if curIsVisibleFrom sc scps then return v else Nothing

instance (Scoped scps, Lookup lkup k v) => Scoped (ScpsLkup lkup scps) where
  empty        = ScpsLkup Lkup.empty empty
  newM         = modL scpslkupScopes new
  popM         = modL scpslkupScopes pop
  switchM      = modL scpslkupScopes . switch
  scope        = scope . getL scpslkupScopes
  curIsVisibleFrom i = curIsVisibleFrom i . getL scpslkupScopes

instance (Scoped scps, Lookup lkup k (ScopedItem v)) => Lookup (ScpsLkup lkup scps) k v where
  lookup k (ScpsLkup lkup scps) = do
    ScopedItem sc v <- lookup k lkup
    whenInScps scps sc v

  alter f k (ScpsLkup lkup scps) =
    ScpsLkup (alter (maybe ((ScopedItem $ scope scps) <$> f Nothing)
                           (\(ScopedItem sc v) -> ScopedItem sc <$> f (Just v))
                    )
                    k lkup
             )
             scps
            
  -- first a quick test, then the more expensive
  null l@(ScpsLkup lkup scps) = null lkup || List.null (toList l)
  
  {-
  -- should restrict to items which are nested inside current scope
  findMin (ScpsLkup lkup scps) = second _scopeditemVal $ findMin lkup
  findMax (ScpsLkup lkup scps) = second _scopeditemVal $ findMax lkup
  -}
  
  toList (ScpsLkup lkup scps) = [ (k,v) | (k, ScopedItem sc v) <- toList lkup, curIsVisibleFrom sc scps ]
  fromList l = (ScpsLkup (fromList $ List.map (\(k,v) -> (k, ScopedItem (scope s) v)) l) s)
    where s = empty

  {-
  -- for performance reasons, should cater for nesting...
  keysSet = keysSet . getL scpslkupBase
  keys    = keys    . getL scpslkupBase
  -}
