{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

{-| Simple term language with some builtin guards and predicates 
 -}

module CHR.Language.Examples.Term.AST
  ( Tm'(..), Tm
  , C'(..), C
  , G'(..), G
  , P'(..), P
  , POp(..)
  , E
  , S', S
  
  , Var
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
import           CHR.Language.GTerm
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

type Key = Key' POp

instance PP op => PP (Key' op) where
  pp (Key_Int i) = pp i
  pp (Key_Var v) = pp v
  pp (Key_Str s) = pp s
  pp (Key_Lst  ) = ppParens "kl"
  pp (Key_Op  o) = pp o
  pp (Key_Con s) = pp s

-- | Terms
data Tm' op
  = Tm_Var Var             -- ^ variable (to be substituted)
  | Tm_Int Int              -- ^ int value (for arithmetic)
  | Tm_Str String
  | Tm_Bool Bool            -- ^ bool value
  | Tm_Con String [Tm' op]      -- ^ general term structure
  | Tm_Lst [Tm' op] (Maybe (Tm' op))  -- ^ special case: list with head segment and term tail
  | Tm_Op  op    [Tm' op]      -- ^ interpretable (when solving) term structure
  deriving (Show, Eq, Ord, Typeable, Generic)

type Tm = Tm' POp

instance VarTerm (Tm' op) where
  varTermMbKey (Tm_Var v) = Just v
  varTermMbKey _          = Nothing
  varTermMkKey            = Tm_Var

instance PP op => PP (Tm' op) where
  pp (Tm_Var v        ) = pp v -- "v" >|< v
  pp (Tm_Con c []     ) = pp c
  pp (Tm_Con c as     ) = ppParens $ c >#< ppSpaces as
  pp (Tm_Lst h mt     ) = let l = ppBracketsCommas h in maybe l (\t -> ppParens $ l >#< ":" >#< t) mt
  pp (Tm_Op  o [a    ]) = ppParens $ o >#< a
  pp (Tm_Op  o [a1,a2]) = ppParens $ a1 >#< o >#< a2
  pp (Tm_Int i        ) = pp i
  pp (Tm_Str s        ) = pp $ show s
  pp (Tm_Bool b       ) = pp b

-- | Constraint
data C' tm
  = C_Con String [tm]
  | CB_Eq tm tm          -- ^ builtin: unification
  | CB_Ne tm tm          -- ^ builtin: non unification
  | CB_Fail              -- ^ explicit fail
  deriving (Show, Eq, Ord, Typeable, Generic)

type C = C' Tm

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

type G = G' Tm

instance PP tm => PP (G' tm) where
  pp (G_Eq x y) = "is-eq" >#< ppParensCommas [x,y]
  pp (G_Ne x y) = "is-ne" >#< ppParensCommas [x,y]
  pp (G_Tm t  ) = "eval"  >#< ppParens t

type instance TrTrKey (Tm' op) = Key' op
type instance TrTrKey (C' (Tm' op)) = Key' op

type instance TT.TrTrKey (Tm' op) = Key' op
type instance TT.TrTrKey (C' (Tm' op)) = Key' op

instance TT.TreeTrieKeyable Tm where
  toTreeTriePreKey1 (Tm_Var  v) = TT.prekey1Wild
  toTreeTriePreKey1 (Tm_Int  i) = TT.prekey1 $ Key_Int i
  toTreeTriePreKey1 (Tm_Str  s) = TT.prekey1 $ Key_Str {- $ "Tm_Str:" ++ -} s
  toTreeTriePreKey1 (Tm_Bool i) = TT.prekey1 $ Key_Int $ fromEnum i
  toTreeTriePreKey1 (Tm_Con c as) = TT.prekey1WithChildren (Key_Str {- $ "Tm_Con:" ++ -} c) as
  toTreeTriePreKey1 (Tm_Op op as) = TT.prekey1WithChildren (Key_Op op) as
  toTreeTriePreKey1 (Tm_Lst h _ ) = TT.prekey1WithChildren Key_Lst h

instance TT.TreeTrieKeyable C where
  -- Only necessary for non-builtin constraints
  toTreeTriePreKey1 (C_Con c as) = TT.prekey1WithChildren (Key_Str {- $ "C_Con:" ++ -} c) as
  toTreeTriePreKey1 _            = TT.prekey1Nil

type E = ()

-- | Binary operator
data POp
  = 
    -- binary
    PBOp_Add
  | PBOp_Sub
  | PBOp_Mul
  | PBOp_Mod
  | PBOp_Lt
  | PBOp_Le
  
    -- unary
  | PUOp_Abs
  deriving (Eq, Ord, Show, Generic)

instance PP POp where
  pp PBOp_Add = pp "+"
  pp PBOp_Sub = pp "-"
  pp PBOp_Mul = pp "*"
  pp PBOp_Mod = pp "mod"
  pp PBOp_Lt  = pp "<"
  pp PBOp_Le  = pp "<="
  pp PUOp_Abs = pp "abs"

newtype P' tm
  = P_Tm tm
  deriving (Eq, Ord, Show, Generic)

type P = P' Tm

instance PP tm => PP (P' tm) where
  pp (P_Tm t) = pp t

instance Bounded (P' (Tm' op)) where
  minBound = P_Tm $ Tm_Int $ fromIntegral $ unPrio $ minBound
  maxBound = P_Tm $ Tm_Int $ fromIntegral $ unPrio $ maxBound

-- type S = IntMap.IntMap Tm
type S' tm = Map.Map Var tm
type S = S' Tm
-- type S = MapH.HashMap Var Tm
-- type S = VAr.VecAlloc Tm
-- type S = Lk.DefaultScpsLkup Var Tm

type instance VarLookupKey (S' tm) = Var
type instance VarLookupVal (S' tm) = tm

instance PP tm => PP (S' tm) where
  pp = ppAssocLV . Lk.toList

type instance ExtrValVarKey (G' tm) = Var
type instance ExtrValVarKey (C' tm) = Var
type instance ExtrValVarKey (Tm' op) = Var
type instance ExtrValVarKey (P'  op) = Var

type instance CHRMatchableKey (S' (Tm' op)) = Key' op

instance VarLookup (S' tm) where
  varlookupWithMetaLev _ = Lk.lookup
  varlookupKeysSetWithMetaLev _ = Lk.keysSet
  varlookupSingletonWithMetaLev _ = Lk.singleton
  varlookupEmpty = Lk.empty

instance Lk.LookupApply (S' tm) (S' tm) where
  apply = Lk.union

instance VarUpdatable tm (S' tm) => VarUpdatable (S' tm) (S' tm) where
  varUpd s = {- Lk.apply s . -} Lk.map (s `varUpd`) -- (|+>)

instance VarUpdatable (Tm' op) (S' (Tm' op)) where
  s `varUpd` t = case fromMaybe t $ Lk.lookupResolveVal varTermMbKey t s of
      Tm_Con c as -> Tm_Con c $ s `varUpd` as
      Tm_Lst h mt -> Tm_Lst (s `varUpd` h) (s `varUpd` mt)
      Tm_Op  o as -> Tm_Op  o $ s `varUpd` as
      t -> t

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

instance VarExtractable (Tm' op) where
  varFreeSet (Tm_Var v) = Set.singleton v
  varFreeSet (Tm_Con _ as) = Set.unions $ map varFreeSet as
  varFreeSet (Tm_Lst h mt) = Set.unions $ map varFreeSet $ maybeToList mt ++ h
  varFreeSet (Tm_Op  _ as) = Set.unions $ map varFreeSet as
  varFreeSet _ = Set.empty

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

instance (TmEvalOp Tm' op, Eq op) => CHRCheckable E (G' (Tm' op)) (S' (Tm' op)) where
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
        case e of
          Tm_Bool True -> chrMatchSuccess
          _            -> chrMatchFail

instance (TmEvalOp Tm' op, Eq op) => CHRMatchable E (Tm' op) (S' (Tm' op)) where
  chrUnifyM how e t1 t2 = case (t1, t2) of
      (Tm_Con c1 as1, Tm_Con c2 as2) | c1 == c2                 -> chrUnifyM how e as1 as2
      (Tm_Lst (h1:t1) mt1, Tm_Lst (h2:t2) mt2)                  -> chrUnifyM how e h1 h2 >> chrUnifyM how e (Tm_Lst t1 mt1) (Tm_Lst t2 mt2)
      (Tm_Lst [] (Just t1), l2@(Tm_Lst {}))                     -> chrUnifyM how e t1 l2
      (l1@(Tm_Lst {}), Tm_Lst [] (Just t2))                     -> chrUnifyM how e l1 t2
      (Tm_Lst [] mt1, Tm_Lst [] mt2)                            -> chrUnifyM how e mt1 mt2
      (Tm_Op  o1 as1, Tm_Op  o2 as2) | how < CHRMatchHow_Unify && o1 == o2
                                                                -> chrUnifyM how e as1 as2
      (Tm_Op  o1 as1, t2           ) | how == CHRMatchHow_Unify -> tmEvalOp o1 as1 >>= \t1 -> chrUnifyM how e t1 t2
      (t1           , Tm_Op  o2 as2) | how == CHRMatchHow_Unify -> tmEvalOp o2 as2 >>= \t2 -> chrUnifyM how e t1 t2
      (Tm_Int i1    , Tm_Int i2    ) | i1 == i2                 -> chrMatchSuccess
      (Tm_Str s1    , Tm_Str s2    ) | s1 == s2                 -> chrMatchSuccess
      (Tm_Bool b1   , Tm_Bool b2   ) | b1 == b2                 -> chrMatchSuccess
      _                                                         -> chrMatchResolveCompareAndContinue how (chrUnifyM how e) t1 t2

tmEval :: TmEvalOp Tm' op => Tm' op -> CHRMatcher (S' (Tm' op)) (Tm' op)
tmEval x = case x of
          Tm_Int _    -> return x
          Tm_Var v    -> Lk.lookupResolveAndContinueM varTermMbKey chrMatchSubst chrMatchFailNoBinding tmEval v
          Tm_Op  o xs -> tmEvalOp o xs
          _           -> chrMatchFail

class TmEvalOp tm op where
  tmEvalOp :: op -> [tm op] -> CHRMatcher (S' (tm op)) (tm op)

instance TmEvalOp Tm' POp where
  -- tmEvalOp :: op -> [Tm' op] -> CHRMatcher (S' (Tm' op)) (Tm' op)
  tmEvalOp o xs = do
            xs <- forM xs tmEval 
            case (o, xs) of
              (PUOp_Abs, [Tm_Int x]) -> ret $ abs x
              (PBOp_Add, [Tm_Int x, Tm_Int y]) -> ret $ x + y
              (PBOp_Sub, [Tm_Int x, Tm_Int y]) -> ret $ x - y
              (PBOp_Mul, [Tm_Int x, Tm_Int y]) -> ret $ x * y
              (PBOp_Mod, [Tm_Int x, Tm_Int y]) -> ret $ x `mod` y
              (PBOp_Lt , [Tm_Int x, Tm_Int y]) -> retb $ x < y
              (PBOp_Le , [Tm_Int x, Tm_Int y]) -> retb $ x <= y
          where ret  x = return $ Tm_Int  x
                retb x = return $ Tm_Bool x


instance (VarExtractable tm, CHRMatchable E tm (S' tm), ExtrValVarKey (C' tm) ~ ExtrValVarKey tm) => CHRMatchable E (C' tm) (S' tm) where
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

instance (VarExtractable tm, CHRMatchable E tm (S' tm), ExtrValVarKey (P' tm) ~ ExtrValVarKey tm) => CHRMatchable E (P' tm) (S' tm) where
  chrUnifyM how e p1 p2 = do
    case (p1, p2) of
      (P_Tm   t1     , P_Tm   t2     ) -> chrUnifyM how e t1  t2

type instance CHRPrioEvaluatableVal (Tm' op) = Prio

instance (TmEvalOp Tm' op) => CHRPrioEvaluatable E (Tm' op) (S' (Tm' op)) where
  chrPrioEval e s t = case chrmatcherRun' (\_ -> Tm_Int $ fromIntegral $ unPrio $ (minBound :: Prio)) (\_ _ x -> x) (tmEval t) emptyCHRMatchEnv (Lk.lifts s) of
    Tm_Int i -> fromIntegral i
    t        -> minBound
  chrPrioLift = Tm_Int . fromIntegral

type instance CHRPrioEvaluatableVal (P' tm) = Prio

instance (CHRPrioEvaluatable E tm (S' tm), CHRPrioEvaluatableVal (P' tm) ~ CHRPrioEvaluatableVal tm) => CHRPrioEvaluatable E (P' tm) (S' tm) where
  chrPrioEval e s p = case p of
    P_Tm t -> chrPrioEval e s t
  chrPrioLift = P_Tm . chrPrioLift


--------------------------------------------------------

instance GTermAs C G P P Tm where
  asHeadConstraint t = case t of
    GTm_Con c a -> forM a asTm >>= (return . C_Con c)
    t -> gtermasFail t "not a constraint"

  asBodyConstraint t = case t of
    GTm_Con "Fail" [] -> return CB_Fail
    GTm_Con o [a,b] | isJust o' -> do
        a <- asTm a
        b <- asTm b
        return $ fromJust o' a b
      where o' = List.lookup o [("==", CB_Eq), ("/=", CB_Ne)]
    t -> asHeadConstraint t

  asGuard t = case t of
    GTm_Con o [a,b] | isJust o' -> do
        a <- asTm a
        b <- asTm b
        return $ fromJust o' a b
      where o' = List.lookup o [("==", G_Eq), ("/=", G_Ne)]
    t -> fmap G_Tm $ asTm t
    
  asHeadBacktrackPrio = fmap P_Tm . asTm

  asAltBacktrackPrio = asHeadBacktrackPrio
  asRulePrio = asHeadBacktrackPrio

  asTm t = case t of
    GTm_Con "True" [] -> return $ Tm_Bool True
    GTm_Con "False" [] -> return $ Tm_Bool False
    GTm_Con o [a] | isJust o' -> do
        a <- asTm a
        return $ Tm_Op (fromJust o') [a]
      where o' = List.lookup o [("Abs", PUOp_Abs)]
    GTm_Con o [a,b] | isJust o' -> do
        a <- asTm a
        b <- asTm b
        return $ Tm_Op (fromJust o') [a,b]
      where o' = List.lookup o [("+", PBOp_Add), ("-", PBOp_Sub), ("*", PBOp_Mul), ("Mod", PBOp_Mod), ("<", PBOp_Lt), ("<=", PBOp_Le)]
    GTm_Con c a -> forM a asTm >>= (return . Tm_Con c)
    GTm_Var v -> -- Tm_Var <$> gtermasVar v
                 return $ Tm_Var v
    GTm_Str v -> return $ Tm_Str v
    GTm_Int i -> return $ Tm_Int (fromInteger i)
    GTm_Nil   -> return $ Tm_Lst [] Nothing
    t@(GTm_Cns _ _) -> asTmList t >>= (return . uncurry Tm_Lst)
    -- t -> gtermasFail t "not a term"

--------------------------------------------------------
-- leq example, backtrack prio specific

