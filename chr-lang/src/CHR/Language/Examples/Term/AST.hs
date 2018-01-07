{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, UndecidableInstances #-}

{-| Simple term language with some builtin guards and predicates 
 -}

module CHR.Language.Examples.Term.AST
  ( Tm'(..), Tm
  , C
  , G
  , P
  , POp(..)
  , S
  , E
    
  , module CHR.Language.WithTerm
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
import           CHR.Language.WithTerm
import qualified CHR.Solve.MonoBacktrackPrio                    as MBP

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

type C = C' Tm

type G = G' Tm

type instance TT.TrTrKey (Tm' op) = Key' op

instance TT.TreeTrieKeyable (Tm' op) where
  toTreeTriePreKey1 (Tm_Var  v) = TT.prekey1Wild
  toTreeTriePreKey1 (Tm_Int  i) = TT.prekey1 $ Key_Int i
  toTreeTriePreKey1 (Tm_Str  s) = TT.prekey1 $ Key_Str s
  toTreeTriePreKey1 (Tm_Bool i) = TT.prekey1 $ Key_Int $ fromEnum i
  toTreeTriePreKey1 (Tm_Con c as) = TT.prekey1WithChildren (Key_Str c) as
  toTreeTriePreKey1 (Tm_Op op as) = TT.prekey1WithChildren (Key_Op op) as
  toTreeTriePreKey1 (Tm_Lst h _ ) = TT.prekey1WithChildren Key_Lst h

type E = E' Tm

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

type P = P' Tm

type S = S' Tm

type instance ExtrValVarKey (Tm' op) = Var

instance VarUpdatable (Tm' op) (S' (Tm' op)) where
  s `varUpd` t = case fromMaybe t $ Lk.lookupResolveVal varTermMbKey t s of
      Tm_Con c as -> Tm_Con c $ s `varUpd` as
      Tm_Lst h mt -> Tm_Lst (s `varUpd` h) (s `varUpd` mt)
      Tm_Op  o as -> Tm_Op  o $ s `varUpd` as
      t -> t

instance VarExtractable (Tm' op) where
  varFreeSet (Tm_Var v) = Set.singleton v
  varFreeSet (Tm_Con _ as) = Set.unions $ map varFreeSet as
  varFreeSet (Tm_Lst h mt) = Set.unions $ map varFreeSet $ maybeToList mt ++ h
  varFreeSet (Tm_Op  _ as) = Set.unions $ map varFreeSet as
  varFreeSet _ = Set.empty

instance (Eq op, TmEval (Tm' op)) => CHRMatchable E (Tm' op) (S' (Tm' op)) where
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

instance TmEval Tm where
  -- tmEval :: TmEvalOp Tm' op => Tm' op -> CHRMatcher (S' (Tm' op)) (Tm' op)
  tmEval x = case x of
          Tm_Int _    -> return x
          Tm_Var v    -> Lk.lookupResolveAndContinueM varTermMbKey chrMatchSubst chrMatchFailNoBinding tmEval v
          Tm_Op  o xs -> tmEvalOp o xs
          _           -> chrMatchFail

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

type instance CHRPrioEvaluatableVal (Tm' op) = Prio


--------------------------------------------------------

type instance TmOp (Tm' op) = op

instance TmMk Tm where
  tmUnaryOps _ = [("Abs", PUOp_Abs)]
  tmBinaryOps _ = [("+", PBOp_Add), ("-", PBOp_Sub), ("*", PBOp_Mul), ("Mod", PBOp_Mod), ("<", PBOp_Lt), ("<=", PBOp_Le)]
  
  mkTmBool = Tm_Bool
  mkTmVar  = Tm_Var
  mkTmStr  = Tm_Str
  mkTmInt  = Tm_Int . fromIntegral
  mkTmCon  = Tm_Con
  mkTmLst  = Tm_Lst
  
  mkTmUnaryOp   = \o a   -> Tm_Op o [a]
  mkTmBinaryOp  = \o a b -> Tm_Op o [a,b]

instance TmValMk Tm where
  valTmMkInt = Tm_Int

instance TmIs Tm where
  isTmInt (Tm_Int v) = Just v
  isTmInt _          = Nothing

  isTmBool (Tm_Bool v) = Just v
  isTmBool _           = Nothing



