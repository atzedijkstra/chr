{-# LANGUAGE FlexibleInstances, UndecidableInstances, ExistentialQuantification, RankNTypes, ScopedTypeVariables #-}

module Control.Monad.LogicState.Examples
  ( main
  )
  where

import           Control.Monad
import           Control.Monad.Trans.Class
import           Control.Monad.State.Strict as StStr
-- import qualified Control.Monad.State.Strict as StStr
import qualified Control.Monad.State.Lazy as StLaz

import           Control.Monad.LogicState.Logic
import           Control.Monad.LogicState


odds :: MonadPlus m => m Int
odds = (return 1) `mplus` (odds >>= \a -> return (2 + a))

{-

-------------------------------------------------------------------------------------------------
-- Basic queens
queens1 :: Int -> [[Int]]
queens1 n = filter test (generate n)
    where generate 0      = [[]]
          generate k      = [q : qs | q <- [1..n], qs <- generate (k-1)]
          test []         = True
          test (q:qs)     = isSafe q qs && test qs
          isSafe   try qs = not (try `elem` qs || sameDiag try qs)
          sameDiag try qs = any (\(colDist,q) -> abs (try - q) == colDist) $ zip [1..] qs

-------------------------------------------------------------------------------------------------
-- Basic queens, optimized with pruning
queens2 :: Int -> [[Int]]
queens2 n = map reverse $ queens' n
    where queens' 0       = [[]]
          queens' k       = [q:qs | qs <- queens' (k-1), q <- [1..n], isSafe q qs]
          isSafe   try qs = not (try `elem` qs || sameDiag try qs)
          sameDiag try qs = any (\(colDist,q) -> abs (try - q) == colDist) $ zip [1..] qs

-------------------------------------------------------------------------------------------------
-- Logic queens
queens1L n = do
    q <- generate1 n n
    guard (test q)
    return q
  where
    test []         = True
    test (q:qs)     = isSafe q qs && test qs
    isSafe   try qs = not (try `elem` qs || sameDiag try qs)
    sameDiag try qs = any (\(colDist,q) -> abs (try - q) == colDist) $ zip [1..] qs

generate1 :: MonadPlus m => Int -> Int -> m [Int]
generate1 _ 0 = return []
generate1 n k = do
  qs <- generate1 n (k-1)
  msum $ map (return . (:qs)) [1..n]

-------------------------------------------------------------------------------------------------
-- Logic queens, with pruning
queens2L n = do
    q <- generate2 n n
    return q

generate2 :: MonadPlus m => Int -> Int -> m [Int]
generate2 _ 0 = return []
generate2 n k = do
    qs <- generate2 n (k-1)
    msum $ flip map [1..n] $ \i -> do
      let q = i : qs
      guard (test q)
      return q
  where
    test []         = True
    test (q:qs)     = isSafe q qs && test qs
    isSafe   try qs = not (try `elem` qs || sameDiag try qs)
    sameDiag try qs = any (\(colDist,q) -> abs (try - q) == colDist) $ zip [1..] qs

-}

-------------------------------------------------------------------------------------------------
-- Logic queens, with pruning, with state
queens3L n = do
    q <- generate3 n n
    return q

count3g :: Monad m => LogicStateT Int Int m Int
count3g = state (\(g::Int, b::Int) -> (g,(g+1,b)))

count3gb :: Monad m => LogicStateT Int Int m (Int,Int)
count3gb = state (\(g::Int, b::Int) -> ((g,b),(g+1,b+1)))

generate3 :: Monad m => Int -> Int -> LogicStateT Int Int m ((Int,Int),[Int])
generate3 _ 0 = count3gb >>= \c -> return (c,[])
generate3 n k = do
    (_,qs) <- generate3 n (k-1)
    qss <- forM [1..n] $ \i -> backtrack $ do
      let q = i : qs
      guard (test q)
      cnt <- count3gb
      return (cnt,q)
    foldr1 mplus qss
{-
    foldr1 mplus $ flip map [1..n] $ \i -> do
      let q = i : qs
      guard (test q)
      cnt <- count3gb
      return (cnt,q)
-}
  where
    test []         = True
    test (q:qs)     = isSafe q qs && test qs
    isSafe   try qs = not (try `elem` qs || sameDiag try qs)
    sameDiag try qs = any (\(colDist,q) -> abs (try - q) == colDist) $ zip [1..] qs


main = do
  -- forM_ (queens1 8) print
  -- forM_ (queens2 8) print
  -- forM_ (observeAll () $ queens1L 8) print
  -- forM_ (observeAll () $ (queens2L 8 :: Logic [Int])) print
  -- forM_ (observeAll (0::Int,0::Int) $ (queens3L 8 :: LogicVar Int Int ((Int,Int),[Int]))) print
  forM_ (observeMany (0::Int,0::Int) 500 $ (queens3L 10 :: LogicState Int Int ((Int,Int),[Int]))) print
  -- forM_ (observe (0::Int,0::Int) $ (queens3L 8 :: LogicVar Int Int ((Int,Int),[Int]))) print
