-------------------------------------------------------------------------------------------
--- Run length encoded list, interpretation/usage as encoding of lexical scope
-------------------------------------------------------------------------------------------

{- |
  LexScope represents a lexical scoping, encoded as a list of Int.
-}

module UHC.Util.RLList.LexScope
  ( -- * Lexical scope
    LexScope
  , enter
  , leave
  
  , isVisibleIn
  , common
  , parents
  
  , compareByLength
  
    -- * Re-export
  , module RLL
  )
  where

import           UHC.Util.RLList as RLL
import           Prelude hiding (concat, null, init, length)
import           Data.Maybe

-------------------------------------------------------------------------------------------
--- Lexical scope: construction
-------------------------------------------------------------------------------------------

type LexScope = RLList Int

-- | Enter a new scope
enter :: Int -> LexScope -> LexScope
enter x s = s `concat` singleton x
{-# INLINE enter #-}

-- | Leave a scope, if possible
leave :: LexScope -> Maybe LexScope
leave s = fmap fst $ initLast s
{-# INLINE leave #-}

-------------------------------------------------------------------------------------------
--- Lexical scope: observations
-------------------------------------------------------------------------------------------

-- | Is scope visible from other scope?
isVisibleIn :: LexScope -> LexScope -> Bool
isVisibleIn sOuter sInner = sOuter `isPrefixOf` sInner
{-# INLINE isVisibleIn #-}

-- | The common outer scope, which is empty if there is no common scope
common :: LexScope -> LexScope -> LexScope
common s1 s2
  = commonPrefix s1 s2
  where commonPrefix xxs yys
          | isJust ht1 && isJust ht2 && x == y = singleton x `concat` commonPrefix xs ys
          | otherwise                          = empty
          where ht1@(~(Just (x,xs))) = headTail xxs
                ht2@(~(Just (y,ys))) = headTail yys

-- | All possible parent scopes
parents :: LexScope -> [LexScope]
parents s | not (null s) = inits $ init s
parents _                = []

-- | Compare by length
compareByLength :: LexScope -> LexScope -> Ordering                  
compareByLength s t = length s `compare` length t
{-# INLINE compareByLength #-}
