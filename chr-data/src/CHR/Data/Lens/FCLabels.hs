{-| Minimal redefine + re-export of a lens package, fclabels
-}

{-# LANGUAGE TypeOperators, NoMonomorphismRestriction #-}

module CHR.Data.Lens.FCLabels
  ( (:->)
  , Lens

  -- * Access
  
  , (^*)

  , (^.)
  , (^=)
  , (^$=)
  , getL
  
  , (=.)
  , (=:)
  , (=$:)
  , modifyAndGet, (=$^:), modL
  , getl
  
  -- * Misc
  
  , focus
  
  , mkLabel
  
  -- * Tuple accessors
  , fstl
  , sndl
  , fst3l
  , snd3l
  , trd3l
  
  -- * Wrappers
  
  , isoMb
  , isoMbWithDefault

  )
  where

import           Prelude hiding ((.), id)
import qualified Control.Monad.State as MS
import           Control.Monad.Trans
import           Control.Category

import           Data.Label hiding (Lens)
import qualified Data.Label.Base as L
import           Data.Label.Monadic((=:), (=.), modifyAndGet)
import qualified Data.Label.Monadic as M
import qualified Data.Label.Partial as P

import           CHR.Utils

-- * Textual alias for (:->), avoiding TypeOperators
type Lens a b = a :-> b

-- * Operator interface for composition

infixl 9 ^*
-- | composition with a flipped reading
(^*) :: (a :-> b) -> (b :-> c) -> (a :-> c)
f1 ^* f2 = f2 . f1
{-# INLINE (^*) #-}


-- * Operator interface for functional part (occasionally similar to Data.Lens)

infixl 8 ^.
-- | functional getter, which acts like a field accessor
(^.) :: a -> (a :-> b) -> b
a ^. f = get f a
{-# INLINE (^.) #-}

-- | Alias for 'get' to avoid conflict with state get; not happy choice because of 'getl'
getL :: (f :-> a) -> f -> a
getL = get
{-# INLINE getL #-}

infixr 4 ^=
-- | functional setter, which acts like a field assigner
(^=) :: (a :-> b) -> b -> a -> a
(^=) = set
{-# INLINE (^=) #-}

infixr 4 ^$=
-- | functional modify
(^$=) :: (a :-> b) -> (b -> b) -> a -> a
(^$=) = modify
{-# INLINE (^$=) #-}

-- * Operator interface for monadic part (occasionally similar to Data.Lens)

infixr 4 =$^:
-- | monadic modify & set & get
(=$^:), modL :: MS.MonadState f m => (f :-> o) -> (o -> (a,o)) -> m a
(=$^:) = M.modifyAndGet
{-# INLINE (=$^:) #-}
modL = M.modifyAndGet
{-# INLINE modL #-}

infixr 4 =$:
-- | monadic modify & set
(=$:) :: MS.MonadState f m => (f :-> o) -> (o -> o) -> m ()
(=$:) = M.modify
{-# INLINE (=$:) #-}

-- | Zoom state in on substructure. This regretfully does not really work, because of MonadState fundep.
focus :: (MS.MonadState a m, MS.MonadState b m) => (a :-> b) -> m c -> m c
focus f m = do
  a <- MS.get
  (b,c) <- do {MS.put (get f a) ; c <- m ; b <- MS.get ; return (b,c)}
  MS.put $ set f b a
  return c
  
{-
 (Lens f) (StateT g) = StateT $ \a -> case f a of
  StoreT (Identity h) b -> liftM (second h) (g b)
-}

-- | Alias for 'gets' avoiding conflict with MonadState
getl :: MS.MonadState f m => (f :-> o) -> m o
getl = M.gets
{-# INLINE getl #-}

-- * Tuple

fstl = L.fst
{-# INLINE fstl #-}

sndl = L.snd
{-# INLINE sndl #-}

fst3l = L.fst3
{-# INLINE fst3l #-}

snd3l = L.snd3
{-# INLINE snd3l #-}

trd3l = L.trd3
{-# INLINE trd3l #-}

-- * Wrappers

-- | Wrapper around a Maybe with a default in case of Nothing
isoMbWithDefault :: o -> (f :-> Maybe o) -> (f :-> o)
isoMbWithDefault dflt f = iso (Iso (maybe dflt id) (Just)) . f

-- | Wrapper around a Maybe with an embedded panic in case of Nothing, with a panic message
isoMb :: String -> (f :-> Maybe o) -> (f :-> o)
isoMb msg f = iso (Iso (panicJust msg) (Just)) . f
