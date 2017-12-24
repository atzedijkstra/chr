{-# LANGUAGE UndecidableInstances, GeneralizedNewtypeDeriving, ScopedTypeVariables, TypeFamilies #-}
{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 710
#else
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | Abstractions for looking up (type) variables in structures

module CHR.Data.VarLookup
    ( VarLookupKey
    , VarLookupVal
    , VarLookup(..)

    -- , varlookupResolveVarWithMetaLev
    -- , varlookupResolveVar
    -- , varlookupResolveValWithMetaLev
    -- , varlookupResolveVal
    -- 
    -- -- , VarCompareHow(..)
    -- 
    -- , varlookupMap
    -- 
    -- , varlookupResolveAndContinueM
    -- 
    -- , VarLookupFix, varlookupFix
    -- , varlookupFixDel
    -- 
    -- , VarLookupCmb (..)     -- 20170107 TBD: should not be both, VarLookupCmb to be replaced by LookupApply
    , LookupApply(..)
    -- 
    -- -- , VarLookupBase (..)
    -- 
    -- , VarLookupCmbFix, varlookupcmbFix
    -- 
    , MetaLev
    , metaLevVal
    -- 
    , StackedVarLookup -- (..)
    
    )
  where

-- import           Control.Applicative
-- import           Data.Maybe
-- import           UHC.Util.Pretty
import           CHR.Data.Lookup.Stacked
import           CHR.Data.Lookup.Types      as Lk
import qualified Data.Set as Set

-------------------------------------------------------------------------------------------
--- Level of lookup
-------------------------------------------------------------------------------------------

-- | Level to lookup into
type MetaLev = Int

-- | Base level (of values, usually)
metaLevVal :: MetaLev
metaLevVal = 0

-------------------------------------------------------------------------------------------
--- VarLookup: something which can lookup a value 'v' given a key 'k'.
-------------------------------------------------------------------------------------------


-- | Type family for key of a VarLookup
type family VarLookupKey m :: *
-- | Type family for value of a VarLookup
type family VarLookupVal m :: *

{- |
VarLookup abstracts from a Map.
The purpose is to be able to combine maps only for the purpose of searching without actually merging the maps.
This then avoids the later need to unmerge such mergings.
The class interface serves to hide this.
-}

class VarLookup m where
  -- | Lookup a key at a level
  varlookupWithMetaLev :: MetaLev -> VarLookupKey m -> m -> Maybe (VarLookupVal m)

  -- | Lookup a key
  varlookup :: VarLookupKey m -> m -> Maybe (VarLookupVal m)
  varlookup = varlookupWithMetaLev metaLevVal
  {-# INLINE varlookup #-}
  
  -- | Keys at a level
  varlookupKeysSetWithMetaLev :: (Ord (VarLookupKey m)) => MetaLev -> m -> Set.Set (VarLookupKey m)
  
  -- | Keys as Set
  varlookupKeysSet :: (Ord (VarLookupKey m)) => m -> Set.Set (VarLookupKey m)
  varlookupKeysSet = varlookupKeysSetWithMetaLev metaLevVal
  {-# INLINE varlookupKeysSet #-}

  -- | Make an empty VarLookup
  varlookupEmpty :: m
  -- | Make a singleton VarLookup at a level
  varlookupSingletonWithMetaLev :: MetaLev -> VarLookupKey m -> VarLookupVal m -> m
  
  -- | Make a singleton VarLookup
  varlookupSingleton :: VarLookupKey m -> VarLookupVal m -> m
  varlookupSingleton = varlookupSingletonWithMetaLev metaLevVal
  {-# INLINE varlookupSingleton #-}

-------------------------------------------------------------------------------------------
--- Util/convenience
-------------------------------------------------------------------------------------------

{-
-- | Combine lookup with map; should be obsolete...
varlookupMap :: VarLookup m => (VarLookupVal m -> Maybe res) -> VarLookupKey m -> m -> Maybe res
varlookupMap get k m = varlookup k m >>= get
{-# INLINE varlookupMap #-}
-}

-------------------------------------------------------------------------------------------
--- Lookup and resolution
-------------------------------------------------------------------------------------------

{-
-- | Fully resolve lookup
varlookupResolveVarWithMetaLev :: VarLookup m => MetaLev -> (VarLookupVal m -> Maybe (VarLookupKey m)) -> VarLookupKey m -> m -> Maybe (VarLookupVal m)
varlookupResolveVarWithMetaLev l isVar k m =
  varlookupWithMetaLev l k m >>= \v -> varlookupResolveValWithMetaLev l isVar v m <|> return v

-- | Fully resolve lookup
varlookupResolveVar :: VarLookup m => (VarLookupVal m -> Maybe (VarLookupKey m)) -> VarLookupKey m -> m -> Maybe (VarLookupVal m)
varlookupResolveVar = varlookupResolveVarWithMetaLev metaLevVal
{-# INLINE varlookupResolveVar #-}

varlookupResolveValWithMetaLev :: VarLookup m => MetaLev -> (VarLookupVal m -> Maybe (VarLookupKey m)) -> VarLookupVal m -> m -> Maybe (VarLookupVal m)
varlookupResolveValWithMetaLev l isVar v m = isVar v >>= \k -> varlookupResolveVarWithMetaLev l isVar k m <|> return v

-- | Fully resolve lookup
varlookupResolveVal :: VarLookup m => (VarLookupVal m -> Maybe (VarLookupKey m)) -> VarLookupVal m -> m -> Maybe (VarLookupVal m)
varlookupResolveVal = varlookupResolveValWithMetaLev metaLevVal
{-# INLINE varlookupResolveVal #-}

-- | Monadically lookup a variable, resolve it, continue with either a fail or success monad continuation
varlookupResolveAndContinueM :: (Monad m, VarLookup s) => (VarLookupVal s -> Maybe (VarLookupKey s)) -> (m s) -> (m a) -> (VarLookupVal s -> m a) -> VarLookupKey s -> m a
varlookupResolveAndContinueM tmIsVar gets failFind okFind k = gets >>= \s -> maybe failFind okFind $ varlookupResolveVar tmIsVar k s
-}

-------------------------------------------------------------------------------------------
--- VarLookupFix
-------------------------------------------------------------------------------------------

{-
-- (not yet, still in use in UHC) {-# DEPRECATED VarLookupFix, varlookupFix, varlookupFixDel "As of 20160331: don't use these anymore" #-}

type VarLookupFix k v = k -> Maybe v

-- | fix looking up to be for a certain var mapping
varlookupFix :: VarLookup m => m -> VarLookupFix (VarLookupKey m) (VarLookupVal m)
varlookupFix m = \k -> varlookup k m

-- | simulate deletion
varlookupFixDel :: Ord k => [k] -> VarLookupFix k v -> VarLookupFix k v
varlookupFixDel ks f = \k -> if k `elem` ks then Nothing else f k
-}

-------------------------------------------------------------------------------------------
--- VarLookupCmb: combine VarLookups
-------------------------------------------------------------------------------------------

{- |
VarLookupCmb abstracts the 'combining' of/from a substitution.
The interface goes along with VarLookup but is split off to avoid functional dependency restrictions.
The purpose is to be able to combine maps only for the purpose of searching without actually merging the maps.
This then avoids the later need to unmerge such mergings.
-}

{-
class VarLookupCmb m1 m2 where
  (|+>) :: m1 -> m2 -> m2

infixr 7 |+>

-- build on LookupApply, if available
instance {-# OVERLAPPABLE #-} Lk.LookupApply m1 m2 => VarLookupCmb m1 m2 where
  (|+>) = Lk.apply
-}

{-
#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPING #-}
#else
instance
#endif
  VarLookupCmb m1 m2 => VarLookupCmb m1 [m2] where
    m1 |+> (m2:m2s) = (m1 |+> m2) : m2s
-}

{-
#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPING #-}
#else
instance
#endif
  (VarLookupCmb m1 m1, VarLookupCmb m1 m2) => VarLookupCmb [m1] [m2] where
    m1 |+> (m2:m2s) = (foldr1 (|+>) m1 |+> m2) : m2s
-}

{-
instance
  (VarLookupCmb m1 m1, VarLookupCmb m1 m2) => VarLookupCmb (StackedVarLookup m1) (StackedVarLookup m2) where
    m1 |+> StackedVarLookup (m2:m2s) = StackedVarLookup $ (foldr1 (|+>) m1 |+> m2) : m2s
-}

-------------------------------------------------------------------------------------------
--- How to do the VarLookup part of matching/unification/comparing
-------------------------------------------------------------------------------------------

{-
-- | How to match, increasingly more binding is allowed
data VarCompareHow
  = VarCompareHow_Check               -- ^ equality check only
  | VarCompareHow_Match               -- ^ also allow one-directional (left to right) matching/binding of (meta)vars
  | VarCompareHow_MatchAndWait        -- ^ also allow giving back of global vars on which we wait
  | VarCompareHow_Unify               -- ^ also allow bi-directional matching, i.e. unification
  deriving (Ord, Eq)
-}

-------------------------------------------------------------------------------------------
--- VarLookupCmbFix
-------------------------------------------------------------------------------------------

{-
{-# DEPRECATED VarLookupCmbFix, varlookupcmbFix "As of 20160331: don't use these anymore" #-}
type VarLookupCmbFix m1 m2 = m1 -> m2 -> m2

-- | fix combining up to be for a certain var mapping
varlookupcmbFix :: VarLookupCmb m1 m2 => VarLookupCmbFix m1 m2
varlookupcmbFix m1 m2 = m1 |+> m2
-}

-------------------------------------------------------------------------------------------
--- Stack of things in which we can lookup, but which is updated only at the top
-------------------------------------------------------------------------------------------

-- | Stacked VarLookup derived from a base one, to allow a use of multiple lookups but update on top only
type StackedVarLookup s = Stacks s

type instance VarLookupKey (StackedVarLookup s) = VarLookupKey s
type instance VarLookupVal (StackedVarLookup s) = VarLookupVal s
type instance StackedElt   (StackedVarLookup s) = s


