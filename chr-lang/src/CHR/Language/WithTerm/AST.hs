{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, UndecidableInstances #-}

{-| Simple term language with some builtin guards and predicates 
 -}

module CHR.Language.WithTerm.AST
  ( Key'(..)
  
  , C'(..)
  , G'(..)
  , P'(..)
  , E'
  , S'
  
  , Var
  
  , TmEval(..)
  
  , TmOp
  )
  where

import           CHR.Data.VarLookup
import qualified CHR.Data.Lookup                                as Lk
import qualified CHR.Data.Lookup.Stacked                        as Lk
import qualified CHR.Data.Lookup.Scoped                         as Lk hiding (empty)
import           CHR.Data.Substitutable
import qualified CHR.Data.TreeTrie                              as TT
import qualified CHR.Data.VecAlloc                              as VAr
import           CHR.Pretty                                     as PP
import           CHR.Types
import           CHR.Types.Core
import           CHR.Utils
import           CHR.Data.AssocL
import           CHR.Data.Lens
import           CHR.Language.Generic
import qualified CHR.Solve.MonoBacktrackPrio  as MBP

import           Data.Typeable
import           Data.Maybe
import qualified Data.Map                                       as Map
import qualified Data.HashMap.Strict                            as MapH
import qualified Data.IntMap                                    as IntMap
import qualified Data.Set                                       as Set
import qualified Data.List                                      as List
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Applicative
import           GHC.Generics                                   (Generic)

-- import           UHC.Util.Debug


type Var = -- IVar
           String

data Key' op
  = Key_Int     !Int            
  | Key_Var     !Var            
  | Key_Str     !String   
  | Key_Lst
  | Key_Op      !op   
  | Key_Con     !String   
  deriving (Eq, Ord, Show)

-- type Key = Key' POp

instance PP op => PP (Key' op) where
  pp (Key_Int i) = pp i
  pp (Key_Var v) = pp v
  pp (Key_Str s) = pp s
  pp (Key_Lst  ) = ppParens "kl"
  pp (Key_Op  o) = pp o
  pp (Key_Con s) = pp s

-- | Constraint
data C' tm
  = C_Con String [tm]
  | CB_Eq tm tm          -- ^ builtin: unification
  | CB_Ne tm tm          -- ^ builtin: non unification
  | CB_Fail              -- ^ explicit fail
  deriving (Show, Eq, Ord, Typeable, Generic)

instance PP tm => PP (C' tm) where
  pp (C_Con c as) = c >#< ppSpaces as
  pp (CB_Eq x y ) = "unify" >#< ppSpaces [x,y]
  pp (CB_Ne x y ) = "not-unify" >#< ppSpaces [x,y]
  pp (CB_Fail   ) = pp "fail"

-- | Guard
data G' tm
  = G_Eq tm tm          -- ^ check for equality
  | G_Ne tm tm          -- ^ check for inequality
  | G_Tm tm             -- ^ determined by arithmetic evaluation
  deriving (Show, Typeable, Generic)

instance PP tm => PP (G' tm) where
  pp (G_Eq x y) = "is-eq" >#< ppParensCommas [x,y]
  pp (G_Ne x y) = "is-ne" >#< ppParensCommas [x,y]
  pp (G_Tm t  ) = "eval"  >#< ppParens t

type instance TT.TrTrKey (C' tm) = Key' (TmOp tm)

instance (TT.TrTrKey (C' tm) ~ TT.TrTrKey tm, TT.TreeTrieKeyable tm) => TT.TreeTrieKeyable (C' tm) where
  -- Only necessary for non-builtin constraints
  toTreeTriePreKey1 (C_Con c as) = TT.prekey1WithChildren (Key_Str c) as
  toTreeTriePreKey1 _            = TT.prekey1Nil

type E' tm = ()

newtype P' tm
  = P_Tm tm
  deriving (Eq, Ord, Show, Generic)

instance PP tm => PP (P' tm) where
  pp (P_Tm t) = pp t

instance TmMk tm => Bounded (P' tm) where
  minBound = P_Tm $ mkTmInt $ fromIntegral $ unPrio $ minBound
  maxBound = P_Tm $ mkTmInt $ fromIntegral $ unPrio $ maxBound

type S' tm = Map.Map Var tm
-- type S = MapH.HashMap Var Tm
-- type S = VAr.VecAlloc Tm
-- type S = Lk.DefaultScpsLkup Var Tm

type instance VarLookupKey (S' tm) = Var
type instance VarLookupVal (S' tm) = tm

instance PP tm => PP (S' tm) where
  pp = ppAssocLV . Lk.toList

type instance ExtrValVarKey (G' tm) = Var
type instance ExtrValVarKey (C' tm) = Var
type instance ExtrValVarKey (P'  tm) = Var

type instance CHRMatchableKey (S' (tm op)) = Key' op

instance VarLookup (S' tm) where
  varlookupWithMetaLev _ = Lk.lookup
  varlookupKeysSetWithMetaLev _ = Lk.keysSet
  varlookupSingletonWithMetaLev _ = Lk.singleton
  varlookupEmpty = Lk.empty

instance Lk.LookupApply (S' tm) (S' tm) where
  apply = Lk.union

instance VarUpdatable tm (S' tm) => VarUpdatable (S' tm) (S' tm) where
  varUpd s = {- Lk.apply s . -} Lk.map (s `varUpd`) -- (|+>)

instance VarUpdatable tm (S' tm) => VarUpdatable (P' tm) (S' tm) where
  s `varUpd` p = case p of
    P_Tm t -> P_Tm (s `varUpd` t)

instance VarUpdatable tm (S' tm) => VarUpdatable (G' tm) (S' tm) where
  s `varUpd` G_Eq x y = G_Eq (s `varUpd` x) (s `varUpd` y)
  s `varUpd` G_Ne x y = G_Ne (s `varUpd` x) (s `varUpd` y)
  s `varUpd` G_Tm x   = G_Tm (s `varUpd` x)

instance VarUpdatable tm (S' tm) => VarUpdatable (C' tm) (S' tm) where
  s `varUpd` c = case c of
    C_Con c as -> C_Con c $ map (s `varUpd`) as
    CB_Eq x y  -> CB_Eq (s `varUpd` x) (s `varUpd` y)
    CB_Ne x y  -> CB_Ne (s `varUpd` x) (s `varUpd` y)
    c          -> c

instance (VarExtractable tm, ExtrValVarKey (G' tm) ~ ExtrValVarKey tm) => VarExtractable (G' tm) where
  varFreeSet (G_Eq x y) = Set.unions [varFreeSet x, varFreeSet y]
  varFreeSet (G_Ne x y) = Set.unions [varFreeSet x, varFreeSet y]
  varFreeSet (G_Tm x  ) = varFreeSet x

instance (VarExtractable tm, ExtrValVarKey (C' tm) ~ ExtrValVarKey tm) => VarExtractable (C' tm) where
  varFreeSet (C_Con _ as) = Set.unions $ map varFreeSet as
  varFreeSet (CB_Eq x y ) = Set.unions [varFreeSet x, varFreeSet y]
  varFreeSet _            = Set.empty

instance (VarExtractable tm, ExtrValVarKey (P' tm) ~ ExtrValVarKey tm) => VarExtractable (P' tm) where
  varFreeSet (P_Tm t) = varFreeSet t

instance CHREmptySubstitution (S' tm) where
  chrEmptySubst = Lk.empty

instance IsConstraint (C' tm) where
  cnstrSolvesVia (C_Con _ _) = ConstraintSolvesVia_Rule
  cnstrSolvesVia (CB_Eq _ _) = ConstraintSolvesVia_Solve
  cnstrSolvesVia (CB_Ne _ _) = ConstraintSolvesVia_Solve
  cnstrSolvesVia (CB_Fail  ) = ConstraintSolvesVia_Fail

instance (CHRMatchable (E' tm) tm (S' tm), TmIs tm, TmEval tm) => CHRCheckable (E' tm) (G' tm) (S' tm) where
  chrCheckM e g =
    case g of
      G_Eq t1 t2 -> chrUnifyM CHRMatchHow_Check e t1 t2
      G_Ne t1 t2 -> do
        menv <- getl chrmatcherstateEnv
        s <- getl chrmatcherstateVarLookup
        chrmatcherRun'
          (\e -> case e of {CHRMatcherFailure -> chrMatchSuccess; _ -> chrMatchFail})
          (\_ _ _ -> chrMatchFail)
          (chrCheckM e (G_Eq t1 t2)) menv s
      G_Tm t -> do
        e <- tmEval t
        case isTmBool e of
          Just True -> chrMatchSuccess
          _         -> chrMatchFail

class TmEval tm where
  tmEval :: tm -> CHRMatcher (S' tm) tm
  tmEvalOp :: TmOp tm -> [tm] -> CHRMatcher (S' tm) tm

instance (VarExtractable tm, CHRMatchable (E' tm) tm (S' tm), ExtrValVarKey (C' tm) ~ ExtrValVarKey tm) => CHRMatchable (E' tm) (C' tm) (S' tm) where
  chrUnifyM how e c1 c2 = do
    case (c1, c2) of
      (C_Con c1 as1, C_Con c2 as2) | c1 == c2 && length as1 == length as2 
        -> sequence_ (zipWith (chrUnifyM how e) as1 as2)
      _ -> chrMatchFail
  chrBuiltinSolveM e b = case b of
    CB_Eq x y -> chrUnifyM CHRMatchHow_Unify e x y
    CB_Ne x y -> do
        menv <- getl chrmatcherstateEnv
        s <- getl chrmatcherstateVarLookup
        chrmatcherRun' (\_ -> chrMatchSuccess) (\_ _ _ -> chrMatchFail) (chrBuiltinSolveM e (CB_Eq x y)) menv s

instance (VarExtractable tm, CHRMatchable (E' tm) tm (S' tm), ExtrValVarKey (P' tm) ~ ExtrValVarKey tm) => CHRMatchable (E' tm) (P' tm) (S' tm) where
  chrUnifyM how e p1 p2 = do
    case (p1, p2) of
      (P_Tm   t1     , P_Tm   t2     ) -> chrUnifyM how e t1  t2

-- type instance CHRPrioEvaluatableVal (Tm' op) = Prio

instance ( TmValMk tm, TmIs tm, TmMk tm, TmEval tm, CHRPrioEvaluatableVal tm ~ Prio
         ) => CHRPrioEvaluatable (E' tm) tm (S' tm) where
  chrPrioEval e s t = case isTmInt $ chrmatcherRun' (\_ -> mkTmInt $ fromIntegral $ unPrio $ (minBound :: Prio)) (\_ _ x -> x) (tmEval t) emptyCHRMatchEnv (Lk.lifts s) of
    Just i -> fromIntegral i
    t      -> minBound
  chrPrioLift _ _ = valTmMkInt . fromIntegral

type instance CHRPrioEvaluatableVal (P' tm) = Prio

instance ( CHRPrioEvaluatable (E' tm) tm (S' tm)
         , TmValMk tm, TmIs tm, TmMk tm, TmEval tm, CHRPrioEvaluatableVal tm ~ Prio
         ) => CHRPrioEvaluatable (E' tm) (P' tm) (S' tm) where
  chrPrioEval e s p = case p of
    P_Tm t -> chrPrioEval e s t
  chrPrioLift e s = P_Tm . chrPrioLift e s


--------------------------------------------------------


instance GTermAsTm tm => GTermAs (C' tm) (G' tm) (P' tm) (P' tm) where
  asHeadConstraint t = case t of
    GTm_Con c a -> forM a asTm >>= (return . C_Con c)
    t -> gtermasFail t "not a constraint"

  asBodyConstraint t = case t of
    GTm_Con "Fail" [] -> return CB_Fail
    GTm_Con o [a,b]
      | Just o' <- List.lookup o [("==", CB_Eq), ("/=", CB_Ne)] -> do
        a <- asTm a
        b <- asTm b
        return $ o' a b
    t -> asHeadConstraint t

  asGuard t = case t of
    GTm_Con o [a,b]
      | Just o' <- List.lookup o [("==", G_Eq), ("/=", G_Ne)] -> do
        a <- asTm a
        b <- asTm b
        return $ o' a b
    t -> fmap G_Tm $ asTm t
    
  asHeadBacktrackPrio = fmap P_Tm . asTm

  asAltBacktrackPrio = asHeadBacktrackPrio
  asRulePrio = asHeadBacktrackPrio



