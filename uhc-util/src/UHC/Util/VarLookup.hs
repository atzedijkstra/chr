{-# LANGUAGE UndecidableInstances #-}

-- | Abstractions for looking up (type) variables in structures

module UHC.Util.VarLookup
    ( module CHR.Data.VarLookup
    
    , VarLookupCmb(..)
    
    , varlookupMap
    )
  where

import           CHR.Data.VarLookup
import qualified CHR.Data.Lookup as Lk

{- |
VarLookupCmb abstracts the 'combining' of/from a substitution.
The interface goes along with VarLookup but is split off to avoid functional dependency restrictions.
The purpose is to be able to combine maps only for the purpose of searching without actually merging the maps.
This then avoids the later need to unmerge such mergings.
-}

class VarLookupCmb m1 m2 where
  (|+>) :: m1 -> m2 -> m2

infixr 7 |+>

-- build on LookupApply, if available
instance {-# OVERLAPPABLE #-} Lk.LookupApply m1 m2 => VarLookupCmb m1 m2 where
  (|+>) = Lk.apply

-------------------------------------------------------------------------------------------
--- Util/convenience
-------------------------------------------------------------------------------------------

-- | Combine lookup with map; should be obsolete...
varlookupMap :: VarLookup m => (VarLookupVal m -> Maybe res) -> VarLookupKey m -> m -> Maybe res
varlookupMap get k m = varlookup k m >>= get
{-# INLINE varlookupMap #-}
