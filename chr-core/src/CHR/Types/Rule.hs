{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies, UndecidableInstances, ExistentialQuantification, ScopedTypeVariables, StandaloneDeriving #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}

-------------------------------------------------------------------------------------------
--- Constraint Handling Rules
-------------------------------------------------------------------------------------------

{- |
The representation of rules, which should allow an implementation of:

"A Flexible Search Framework for CHR", Leslie De Koninck, Tom Schrijvers, and Bart Demoen.
http://link.springer.com/10.1007/978-3-540-92243-8_2

-}

module CHR.Types.Rule
  ( RuleBodyAlt(..)
  
  , Rule(..)
  , ruleBody, ruleBody'
  , ruleSz
    
  , (/\)
  , (\/)
  , (\!)
  , (<=>>), (==>>), (<\>>)
  , (<==>), (<=>), (==>), (<\>)
  , (|>), (=|)
  , (=!), (=!!)
  , (=@), (@=)
  )
  where

import           Data.Monoid
import           Data.List as List
import           Data.Typeable
import qualified Data.Set as Set

import qualified CHR.Data.TreeTrie              as TT
import           CHR.Data.VarMp
import           CHR.Utils
import           CHR.Pretty
import           CHR.Data.Substitutable

import           Control.Monad

-------------------------------------------------------------------------------------------
--- CHR, derived structures
-------------------------------------------------------------------------------------------

data RuleBodyAlt cnstr bprio
  = RuleBodyAlt
      { rbodyaltBacktrackPrio       :: !(Maybe bprio)        -- ^ optional backtrack priority, if absent it is inherited from the active backtrack prio
      , rbodyaltBody                :: ![cnstr]             -- ^ body constraints to be dealt with by rules
      -- , rbodyaltBodyBuiltin         :: ![builtin]           -- ^ builtin constraints to be dealt with by builtin solving
      }
  deriving (Typeable)

instance Show (RuleBodyAlt c bp) where
  show _ = "RuleBodyAlt"

instance (PP bp, PP c) => PP (RuleBodyAlt c bp) where
  pp a = ppParens (rbodyaltBacktrackPrio a) >#< ppCommas' (rbodyaltBody a)

-- | A CHR (rule) consist of head (simplification + propagation, boundary indicated by an Int), guard, and a body. All may be empty, but not all at the same time.
data Rule cnstr guard bprio prio
  = Rule
      { ruleHead            :: ![cnstr]
      , ruleSimpSz          :: !Int                -- ^ length of the part of the head which is the simplification part
      , ruleGuard           :: ![guard]    
      , ruleBodyAlts        :: ![RuleBodyAlt cnstr bprio]
      , ruleBacktrackPrio   :: !(Maybe bprio)      -- ^ backtrack priority, should be something which can be substituted with the actual prio, later to be referred to at backtrack prios of alternatives
      , rulePrio            :: !(Maybe prio)       -- ^ rule priority, to choose between rules with equal backtrack priority
      , ruleName            :: (Maybe String)
      }
  deriving (Typeable)

-- | Backwards compatibility: if only one alternative, extract it, ignore other alts
ruleBody' :: Rule c g bp p -> ([c],[c])
ruleBody' (Rule {ruleBodyAlts = (a:_)}) = (rbodyaltBody a, [])
ruleBody' (Rule {ruleBodyAlts = []   }) = ([], [])

-- | Backwards compatibility: if only one alternative, extract it, ignore other alts
ruleBody :: Rule c g bp p -> [c]
ruleBody = fst . ruleBody'
{-# INLINE ruleBody #-}


-- | Total nr of cnstrs in rule
ruleSz :: Rule c g bp p -> Int
ruleSz = length . ruleHead
{-# INLINE ruleSz #-}

emptyCHRGuard :: [a]
emptyCHRGuard = []

instance Show (Rule c g bp p) where
  show _ = "Rule"

instance (PP c, PP g, PP p, PP bp) => PP (Rule c g bp p) where
  pp chr = ppMbPre (\p -> p >#< "::") rPrio $ ppMbPre (\n -> pp n >#< "@") (ruleName chr) $ base
    where base = case chr of
            Rule {} | ruleSimpSz chr == 0                        -> ppChr ([ppL (ruleHead chr), pp "==>"] ++ ppGB (ruleGuard chr) body)
                    | ruleSimpSz chr == length (ruleHead chr)    -> ppChr ([ppL (ruleHead chr), pp "<=>"] ++ ppGB (ruleGuard chr) body)
                    | length (ruleHead chr) == 0                 -> ppChr (ppGB (ruleGuard chr) body)
                    | otherwise                                  -> ppChr ([ppL (drop (ruleSimpSz chr) (ruleHead chr)), pp "\\", ppL (take (ruleSimpSz chr) (ruleHead chr)), pp "<=>"] ++ ppGB (ruleGuard chr) body)
          rPrio = case (ruleBacktrackPrio chr, rulePrio chr) of
            (Nothing, Nothing) -> Nothing
            (Just bp, Just rp) -> Just $ ppParensCommas [pp bp , pp rp ]
            (Just bp, _      ) -> Just $ ppParensCommas [pp bp , pp "_"]
            (_      , Just rp) -> Just $ ppParensCommas [pp "_", pp rp ]
          body = ppSpaces $ intersperse (pp "\\/") $ map ppAlt $ ruleBodyAlts chr
            where ppAlt a = ppMbPre (\p -> ppParens p >#< "::") (rbodyaltBacktrackPrio a) $ ppL $ map pp (rbodyaltBody a) -- ++ map pp (rbodyaltBodyBuiltin a)
          ppGB g@(_:_) b = [ppL g, "|" >#< b] -- g b = ppListPre (\g -> ppL g >#< "|") g
          ppGB []      b = [b]
          -- ppL [x] = pp x
          ppL xs  = ppCommas' xs -- ppParensCommasBlock xs
          ppChr l = ppSpaces l -- vlist l -- ppCurlysBlock

-- type instance TTKey (Rule cnstr guard bprio prio) = TTKey cnstr
type instance TT.TrTrKey (Rule cnstr guard bprio prio) = TT.TrTrKey cnstr

instance (TT.TreeTrieKeyable cnstr) => TT.TreeTrieKeyable (Rule cnstr guard bprio prio) where
  toTreeTriePreKey1 chr = TT.prekey1Delegate $ head $ ruleHead chr

-------------------------------------------------------------------------------------------
--- Var instances
-------------------------------------------------------------------------------------------

type instance ExtrValVarKey (Rule c g bp p) = ExtrValVarKey c
type instance ExtrValVarKey (RuleBodyAlt c p) = ExtrValVarKey c

-- TBD: should vars be extracted from prio and builtin as well?
instance (VarExtractable c) => VarExtractable (RuleBodyAlt c p) where
  varFreeSet          (RuleBodyAlt {rbodyaltBody=b})
    = Set.unions $ map varFreeSet b

-- TBD: should vars be extracted from prio as well?
instance (VarExtractable c, VarExtractable g, ExtrValVarKey c ~ ExtrValVarKey g) => VarExtractable (Rule c g bp p) where
  varFreeSet          (Rule {ruleHead=h, ruleGuard=g, ruleBodyAlts=b})
    = Set.unions $ concat [map varFreeSet h, map varFreeSet g, map varFreeSet b]

instance (VarUpdatable c s, VarUpdatable p s) => VarUpdatable (RuleBodyAlt c p) s where
  varUpd s r@(RuleBodyAlt {rbodyaltBacktrackPrio=p, rbodyaltBody=b})
    = r {rbodyaltBacktrackPrio = fmap (varUpd s) p, rbodyaltBody = map (varUpd s) b}

instance (VarUpdatable c s, VarUpdatable g s, VarUpdatable bp s, VarUpdatable p s) => VarUpdatable (Rule c g bp p) s where
  varUpd s r@(Rule {ruleHead=h, ruleGuard=g, ruleBodyAlts=b})
    = r {ruleHead = map (varUpd s) h, ruleGuard = map (varUpd s) g, ruleBodyAlts = map (varUpd s) b}

-------------------------------------------------------------------------------------------
--- Construction: Rule
-------------------------------------------------------------------------------------------
  
mkRule h l g b bi p = Rule h l g [RuleBodyAlt Nothing b] Nothing p Nothing
guardRule g r = r {ruleGuard = ruleGuard r ++ g}
prioritizeRule p r = r {rulePrio = Just p}
prioritizeBacktrackRule p r = r {ruleBacktrackPrio = Just p}
labelRule l r = r {ruleName = Just l}


infixl  6 /\
infixl  5 \!
infixr  4 \/
infix   3 <==>, <=>, ==>, <\>
infixl  2 |>, =|
infixl  2 =!, =!!
infixl  2 =@
infixr  1 @=

-- | Rule body backtracking alternative
(/\) :: [c] -> [c] -> RuleBodyAlt c p
c /\ b = RuleBodyAlt Nothing (c ++ b)

-- | Rule body backtracking alternatives
(\/) :: [RuleBodyAlt c p] -> [RuleBodyAlt c p] -> [RuleBodyAlt c p]
(\/) = (++)

-- | Add backtrack priority to body alternative
(\!) :: RuleBodyAlt c p -> p -> RuleBodyAlt c p
r \! p = r {rbodyaltBacktrackPrio = Just p}

-- | Construct simplification rule out of head, body, and builtin constraints
hs <=>>  (bs,bis) = mkRule hs (length hs) [] bs bis Nothing
-- | Construct propagation rule out of head, body, and builtin constraints
hs  ==>>  (bs,bis) = mkRule hs 0 [] bs bis Nothing

-- | Construct simpagation rule out of head, body, and builtin constraints
(hsprop,hssimp) <\>>  (bs,bis) = mkRule (hssimp ++ hsprop) (length hssimp) [] (bs) (bis) Nothing

-- | Construct simplification rule out of head and body constraints
hs <==>  bs = mkRule (hs) (length hs) [] (bs) [] Nothing
-- | Construct propagation rule out of head and body constraints
hs  ==>  bs = mkRule (hs) 0 [] (bs) [] Nothing
(<=>) = (<==>)

-- | Construct simpagation rule out of head and body constraints
(hsprop,hssimp) <\>  bs = mkRule (hssimp ++ hsprop) (length hssimp) [] (bs) [] Nothing

{-# DEPRECATED (|>) "Use (=|)" #-}
-- | Add guards to rule
r |> g = guardRule (g) r
(=|) = (|>)
{-# INLINE (=|) #-}

-- | Add priority to rule
r =!! p = prioritizeRule (p) r

-- | Add backtrack priority to rule
r =! p = prioritizeBacktrackRule (p) r

-- | Add label to rule
r =@ l = labelRule l r

-- | Add label to rule
l @= r = r =@ l
{-# INLINE (@=) #-}

