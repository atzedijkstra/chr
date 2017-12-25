-------------------------------------------------------------------------------------------
--- Substitution abilities
-------------------------------------------------------------------------------------------

{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}

module CHR.Data.Substitutable
  (
    VarUpdatable(..)
  , VarExtractable(..)
  
  , ExtrValVarKey
  
  , VarTerm(..)
  )
  where

import qualified Data.Set as Set
import           CHR.Data.VarMp

-------------------------------------------------------------------------------------------
--- Misc
-------------------------------------------------------------------------------------------

infixr 6 `varUpd`
infixr 6 `varUpdCyc`

-- | The variable wich is used as a key into a substitution
type family ExtrValVarKey vv :: *

-------------------------------------------------------------------------------------------
--- Updatable
-------------------------------------------------------------------------------------------

-- | Term in which variables can be updated with a subst(itution)
class VarUpdatable vv subst where
  -- | Update
  varUpd            ::  subst -> vv -> vv
  -- s `varUpd` x = let (x',_) = s `varUpdCyc` x in x
  -- {-# INLINE varUpd #-}

  -- | Update with cycle detection
  varUpdCyc         ::  subst -> vv -> (vv, VarMp' (VarLookupKey subst) (VarLookupVal subst))
  s `varUpdCyc` x = (s `varUpd` x, emptyVarMp)
  {-# INLINE varUpdCyc #-}

instance {-# OVERLAPPABLE #-} VarUpdatable vv subst => VarUpdatable (Maybe vv) subst where
  s `varUpd`    m = fmap (s `varUpd`) m

  s `varUpdCyc` (Just x) = let (x',cm) = s `varUpdCyc` x in (Just x', cm)
  s `varUpdCyc` Nothing  = (Nothing, emptyVarMp)

instance {-# OVERLAPPABLE #-} (Ord (VarLookupKey subst), VarUpdatable vv subst) => VarUpdatable [vv] subst where
  s `varUpd`    l = map (s `varUpd`) l
  s `varUpdCyc` l = let (l',cms) = unzip $ map (s `varUpdCyc`) l in (l', varmpUnions cms)

-------------------------------------------------------------------------------------------
--- Extractibility of free vars
-------------------------------------------------------------------------------------------

-- | Term from which free variables can be extracted
class Ord (ExtrValVarKey vv) => VarExtractable vv where
  -- | Free vars, as a list
  varFree           ::  vv -> [ExtrValVarKey vv]
  varFree           =   Set.toList . varFreeSet
  
  -- | Free vars, as a set
  varFreeSet        ::  vv -> Set.Set (ExtrValVarKey vv)
  varFreeSet        =   Set.fromList . varFree

type instance ExtrValVarKey (Maybe vv) = ExtrValVarKey vv

instance {-# OVERLAPPABLE #-} (VarExtractable vv, Ord (ExtrValVarKey vv)) => VarExtractable (Maybe vv) where
  varFreeSet        =   maybe Set.empty varFreeSet

type instance ExtrValVarKey [vv] = ExtrValVarKey vv

instance {-# OVERLAPPABLE #-} (VarExtractable vv, Ord (ExtrValVarKey vv)) => VarExtractable [vv] where
  varFreeSet        =   Set.unions . map varFreeSet

-------------------------------------------------------------------------------------------
--- Is a term with a variable which we can observe and construct
-------------------------------------------------------------------------------------------

-- | Term with a (substitutable, extractable, free, etc.) variable
class VarTerm vv where
  -- | Maybe is a key
  varTermMbKey :: vv -> Maybe (ExtrValVarKey vv)
  -- | Construct wrapper for key (i.e. lift, embed)
  varTermMkKey :: ExtrValVarKey vv -> vv
  


