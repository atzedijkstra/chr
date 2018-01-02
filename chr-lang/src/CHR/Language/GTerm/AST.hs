{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

-------------------------------------------------------------------------------------------
--- Generic terms describing constraints, providing interpretation to AST of your choice
-------------------------------------------------------------------------------------------

module CHR.Language.GTerm.AST
  ( GTm(..)
  
  , GTermAs(..)
  , GTermAsTm(..)
  
  , GTermAsM
  
  , GTermAsState(..)
  , emptyGTermAsState
  
  , gtermasVar
  
  , gtermasFail
  )
  where

import           Data.Char
import           Data.Typeable
import           GHC.Generics
import           Control.Monad.Except
import           Control.Monad.State
-- import qualified Data.Map                   as Map
import qualified Data.HashMap.Strict        as MapH

import           CHR.Pretty                 as PP
import           CHR.Utils
import           CHR.Data.Lens
import           CHR.Types
import qualified CHR.Data.Lookup            as Lk
-- import           CHR.Types.Core

-------------------------------------------------------------------------------------------
--- Supporting types
-------------------------------------------------------------------------------------------

data GTermAsState
  = GTermAsState
      { _gtermasNmToVarMp       :: NmToVarMp
      }

emptyGTermAsState :: GTermAsState
emptyGTermAsState = GTermAsState emptyNmToVarMp
      
-------------------------------------------------------------------------------------------
--- Lens
-------------------------------------------------------------------------------------------

mkLabel ''GTermAsState

-------------------------------------------------------------------------------------------
--- Term language/AST
-------------------------------------------------------------------------------------------

-- | Terms
data GTm
  = GTm_Var     String                  -- ^ variable (to be substituted)
  | GTm_Int     Integer                 -- ^ int value (for arithmetic)
  | GTm_Str     String                  -- ^ string value
  | GTm_Con     String [GTm]            -- ^ general term structure
  | GTm_Nil                             -- ^ special case: list nil
  | GTm_Cns     GTm GTm                 -- ^ special case: list cons
  deriving (Show, Eq, Ord, Typeable, Generic)

instance PP GTm where
  pp (GTm_Var v        ) = pp v -- "v" >|< v
  pp (GTm_Con c []     ) = pp c
  pp (GTm_Con c@(h:_) [a1,a2])
    | not (isAlpha h)    = ppParens $ a1 >#< c >#< a2
  pp (GTm_Con c as     ) = ppParens $ c >#< ppSpaces as
  pp (GTm_Nil          ) = pp "[]"
  pp (GTm_Cns h t      ) = "[" >|< h >#< ":" >#< t >|< "]"
  pp (GTm_Int i        ) = pp i
  pp (GTm_Str s        ) = pp $ show s

-------------------------------------------------------------------------------------------
--- Term interpretation in context of CHR
-------------------------------------------------------------------------------------------

-- | Interpretation monad, which is partial
type GTermAsM = StateT GTermAsState (Either PP_Doc)

class GTermAsTm tm where
  asTm :: GTm -> GTermAsM tm

-- | Term interpretation in context of CHR
class GTermAsTm tm => GTermAs cnstr guard bprio prio tm
  | cnstr -> guard bprio prio tm
  , guard -> cnstr bprio prio tm
  , bprio -> cnstr guard prio tm
  , prio -> cnstr guard bprio tm
  , tm -> cnstr guard bprio prio
  where
  --
  -- asTm :: GTm -> GTermAsM tm
  -- | as list, if matches/possible. Only to be invoked for GTm_Cns 
  asTmList :: GTm -> GTermAsM ([tm], Maybe tm)
  asTmList (GTm_Cns h    GTm_Nil     ) = asTm h >>= \h -> return ([h], Nothing)
  asTmList (GTm_Cns h t@(GTm_Cns _ _)) = asTm h >>= \h -> asTmList t >>= \(t,mt) -> return ((h:t),mt)
  asTmList (GTm_Cns h t              ) = asTm h >>= \h -> asTm     t >>= \t -> return ([h], Just t)
  asTmList _                           = panic "GTermAs.asTmList: should not happen, not intended to be called with non GTm_Cns"
  --
  asHeadConstraint :: GTm -> GTermAsM cnstr
  --
  asBodyConstraint :: GTm -> GTermAsM cnstr
  --
  asGuard :: GTm -> GTermAsM guard
  --
  asHeadBacktrackPrio :: GTm -> GTermAsM bprio
  --
  asAltBacktrackPrio :: GTm -> GTermAsM bprio
  --
  asRulePrio :: GTm -> GTermAsM prio

--
gtermasVar :: String -> GTermAsM IVar
gtermasVar s = modL gtermasNmToVarMp $ \m -> maybe (let i = Lk.size m in (i, Lk.insert s i m)) (,m) $ Lk.lookup s m
  
  -- insertLookupWithKey :: Ord k => (k -> a -> a -> a) -> k -> a -> Map k a -> (Maybe a, Map k a)

-- | Fail the interpretation
gtermasFail :: GTm -> String -> GTermAsM a
gtermasFail t m = throwError $ "GTerm interpretation failure" >-< indent 2 ("why :" >#< m >-< "term:" >#< t)
