-------------------------------------------------------------------------------------------
-- Abstraction of Map like datatypes providing lookup
-------------------------------------------------------------------------------------------

module CHR.Data.Lookup
  (
    module CHR.Data.Lookup.Types
  , module CHR.Data.Lookup.Instances
  , module CHR.Data.Lookup.Scoped
  , module CHR.Data.Lookup.Stacked
  
  , lookupResolveVar
  , lookupResolveVal
  , lookupResolveAndContinueM
  
  , inverse
  )
  where

-------------------------------------------------------------------------------------------
import           Prelude                        hiding (lookup, map)
import qualified Data.List                      as List
import           Control.Applicative
import           CHR.Data.Lookup.Types
import           CHR.Data.Lookup.Instances
import           CHR.Data.Lookup.Scoped         (Scoped)
import           CHR.Data.Lookup.Stacked        (Stacked)
import           CHR.Data.VarLookup             (VarLookupKey, VarLookupVal)
-------------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------------
--- Lookup and resolution
-------------------------------------------------------------------------------------------

-- | Fully resolve lookup
lookupResolveVar :: Lookup m (VarLookupKey m) (VarLookupVal m) => (VarLookupVal m -> Maybe (VarLookupKey m)) -> VarLookupKey m -> m -> Maybe (VarLookupVal m)
lookupResolveVar isVar k m = lookup k m >>= \v -> lookupResolveVal isVar v m <|> return v

-- | Fully resolve lookup
lookupResolveVal :: Lookup m (VarLookupKey m) (VarLookupVal m) => (VarLookupVal m -> Maybe (VarLookupKey m)) -> VarLookupVal m -> m -> Maybe (VarLookupVal m)
lookupResolveVal isVar v m = isVar v >>= \k -> lookupResolveVar isVar k m <|> return v

-- | Monadically lookup a variable, resolve it, continue with either a fail or success monad continuation
lookupResolveAndContinueM :: (Monad m, Lookup s (VarLookupKey s) (VarLookupVal s)) => (VarLookupVal s -> Maybe (VarLookupKey s)) -> (m s) -> (m a) -> (VarLookupVal s -> m a) -> VarLookupKey s -> m a
lookupResolveAndContinueM tmIsVar gets failFind okFind k = gets >>= \s -> maybe failFind okFind $ lookupResolveVar tmIsVar k s

-------------------------------------------------------------------------------------------
--- Utils
-------------------------------------------------------------------------------------------

-- | Inverse of a lookup
inverse :: (Lookup l1 k1 v1, Lookup l2 k2 v2) => (k1 -> v1 -> (k2,v2)) -> l1 -> l2
inverse mk = fromList . List.map (uncurry mk) . toList

