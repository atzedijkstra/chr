{-| Minimal redefine + re-export of a lens package, fclabels
-}

{-# LANGUAGE TypeOperators, RankNTypes #-}

module CHR.Data.Lens.MicroLens
  ( 
    (:->)
  , Lens
  -- , lens

  -- * Access
  
  , (^*)

  , (^.)
  , getL
  , (^=)
  , (^$=)
  
  {-
  
  , (=.)
  -}
  , (=:)
  , (=$:)
  , modifyAndGet
  , (=$^:)
  , modL
  , getl
  
  -- * Misc
  
  {-
  , focus
  -}
  
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

import qualified Control.Monad.State as MS
import           Lens.Micro                 hiding (Lens, lens)
import qualified Lens.Micro                 as L
import           Lens.Micro.Mtl
import           Lens.Micro.TH
import           Language.Haskell.TH

import           CHR.Utils

-- * Type aliases
type Lens a b = Lens' a b
type a :-> b = Lens' a b

lens :: (a -> b) -> (a -> b -> a) -> (a :-> b)
lens = L.lens
{-# INLINE lens #-}

-- * Operator interface for composition

infixl 9 ^*
-- | composition alias
(^*) :: (a :-> b) -> (b :-> c) -> (a :-> c)
f1 ^* f2 = f1 . f2
{-# INLINE (^*) #-}

{-

-- * Operator interface for functional part (occasionally similar to Data.Lens)

infixl 8 ^.
-- | functional getter, which acts like a field accessor
(^.) :: a -> (a :-> b) -> b
a ^. f = get f a
{-# INLINE (^.) #-}

-}

-- | Alias for 'get' to avoid conflict with state get; not happy choice because of 'getl'
getL :: (f :-> a) -> f -> a
getL = flip (^.)
{-# INLINE getL #-}

infixr 4 ^=
-- | functional setter, which acts like a field assigner
(^=) :: (a :-> b) -> b -> a -> a
(^=) = set
{-# INLINE (^=) #-}

infixr 4 ^$=
-- | functional modify
(^$=) :: (a :-> b) -> (b -> b) -> a -> a
(^$=) = over
{-# INLINE (^$=) #-}

{-
-}
-- * Operator interface for monadic part (occasionally similar to Data.Lens)

infixr 4 =$^:
-- | monadic modify & set & get
(=$^:), modL, modifyAndGet :: MS.MonadState f m => (f :-> o) -> (o -> (a,o)) -> m a
l =$^: f = do
    old <- use l
    let (res,new) = f old
    l =: new
    return res
{-# INLINE (=$^:) #-}
modL = (=$^:)
{-# INLINE modL #-}
modifyAndGet = (=$^:)
{-# INLINE modifyAndGet #-}

-- | monadic get
getl :: MS.MonadState f m => (f :-> o) -> m o
getl = use

infixr 4 =:
-- | monadic set
(=:) :: MS.MonadState f m => (f :-> o) -> o -> m ()
(=:) = (.=)
{-# INLINE (=:) #-}

infixr 4 =$:
-- | monadic modify & set
(=$:) :: MS.MonadState f m => (f :-> o) -> (o -> o) -> m ()
(=$:) = modifying
{-# INLINE (=$:) #-}

{-

-- | Zoom state in on substructure. This regretfully does not really work, because of MonadState fundep.
focus :: (MS.MonadState a m, MS.MonadState b m) => (a :-> b) -> m c -> m c
focus f m = do
  a <- MS.get
  (b,c) <- do {MS.put (get f a) ; c <- m ; b <- MS.get ; return (b,c)}
  MS.put $ set f b a
  return c

-- | Alias for 'gets' avoiding conflict with MonadState
getl :: MS.MonadState f m => (f :-> o) -> m o
getl = M.gets
{-# INLINE getl #-}

-}

-- * Misc

mkLabel :: Name -> Q [Dec]
mkLabel = makeLenses

-- * Tuple

fstl :: Lens (a,b) a
fstl = (_1)
{-# INLINE fstl #-}

sndl :: Lens (a,b) b
sndl = (_2)
{-# INLINE sndl #-}

fst3l :: Lens (a,b,c) a
fst3l = (_1)
{-# INLINE fst3l #-}

snd3l :: Lens (a,b,c) b
snd3l = (_2)
{-# INLINE snd3l #-}

trd3l :: Lens (a,b,c) c
trd3l = (_3)
{-# INLINE trd3l #-}

-- * Wrappers

-- | Wrapper around a Maybe with a default in case of Nothing
isoMbWithDefault :: o -> (f :-> Maybe o) -> (f :-> o)
-- isoMbWithDefault dflt f = iso (Iso (maybe dflt id) (Just)) . f
isoMbWithDefault dflt f = lens (\a -> maybe dflt id $ a ^. f) (\a b -> set f (Just b) a)

-- | Wrapper around a Maybe with an embedded panic in case of Nothing, with a panic message
isoMb :: String -> (f :-> Maybe o) -> (f :-> o)
-- isoMb msg f = iso (Iso (panicJust msg) (Just)) . f
isoMb msg f = lens (\a -> panicJust msg $ a ^. f) (\a b -> set f (Just b) a)
