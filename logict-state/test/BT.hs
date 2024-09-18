{-# LANGUAGE FlexibleInstances, UndecidableInstances, ExistentialQuantification, RankNTypes, MultiParamTypeClasses, ScopedTypeVariables #-}

module Main
  ( main
  )
  where

import           Control.Monad
import           Control.Monad.Trans.Class
import           Control.Monad.State.Strict as StStr
-- import qualified Control.Monad.State.Strict as StStr
import qualified Control.Monad.State.Lazy as StLaz

import           Control.Monad.Stepwise.Core
import           Control.Monad.Stepwise.Derived

import           Control.Monad.LogicState
import qualified Control.Monad.LogicState.Examples as E


{-
class Observe t where
  observe :: Monad m => t m a -> m a

class Promote t where
  promote :: Monad m => m a -> t m a

instance {-# OVERLAPPABLE #-} MonadTrans t => Promote t where
  promote = lift
  {-# INLINE promote #-}

newtype BackT m a = BackT {runBackT :: forall b . (a -> m b -> m b) -> m b -> m b}

instance Monad m => Monad (BackT m) where
  return a = BackT $ \c f -> c a f
  m >>= k = BackT $ \c f -> runBackT m (\a -> runBackT (k a) c) f

instance Monad m => Applicative (BackT m) where
  pure = return
  (<*>) = ap

instance Functor (BackT m) where
  fmap f bt = BackT $ \c f' -> runBackT bt (c . f) f'

-}

odds :: MonadPlus m => m Int
odds = (return 1) `mplus` (odds >>= \a -> return (2 + a))

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

-------------------------------------------------------------------------------------------------
-- Stepwise queens
queens4S n = do
    q <- generate4 n n
    return q

--
data I t = I

-- | Monoid instance for use in combination with '<|>'. In practice, you'll not
--   use '<|>', but write more complicated merging strategies instead.
instance Monoid (I t) where
  mempty = I
  I `mappend` I = I

generate4 :: Int -> Int -> Stepwise AnyFailure [] any AnyWatcher [Int]
generate4 _ 0 = return []
generate4 n k = do
    qs <- generate4 n (k-1)
    msum $ flip map [1..n] $ \i -> do
      let q = i : qs
      if (test q)
        then return q
        else fail $ "generate4: " ++ show q
  where
    test []         = True
    test (q:qs)     = isSafe q qs && test qs
    isSafe   try qs = not (try `elem` qs || sameDiag try qs)
    sameDiag try qs = any (\(colDist,q) -> abs (try - q) == colDist) $ zip [1..] qs

--
{-
type BackGlobState = Int

emptyBackGlobState :: BackGlobState
emptyBackGlobState = 0

type BackTrackState = [(Int,Int)]

emptyBackTrackState :: BackTrackState
emptyBackTrackState = []

data BackState = BackState
    { bsGlob        :: BackGlobState
    , bsBack        :: BackTrackState
    }

emptyBackState :: BackState
emptyBackState = BackState emptyBackGlobState emptyBackTrackState

newtype BackT  m a = BackT  { runBackT  :: StStr.StateT BackGlobState (LogicT (StLaz.StateT BackTrackState m)) a}
newtype BackT' m a = BackT' { runBackT' :: BackGlobState -> LogicT (StLaz.StateT BackTrackState m) (a, BackGlobState)}
  -- deriving (StStr.MonadState)

observeBackT :: Monad m => BackT m a -> m [a]
observeBackT b = flip StLaz.evalStateT emptyBackTrackState $ observeAllT () $ flip StStr.evalStateT emptyBackGlobState $ runBackT b

instance Functor (BackT m) where
  fmap f (BackT m) = BackT (fmap f m)

instance Monad m => Applicative (BackT m) where
  pure = return
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad m => Monad (BackT m) where
  return  = BackT . return
  m >>= k = BackT $ runBackT m >>= (runBackT . k)

instance MonadTrans BackT where
  lift = BackT . lift . lift . lift
  {-# INLINE lift #-}

instance Monad m => MonadState BackGlobState (BackT m) where
  get = StStr.get
  put = StStr.put

instance Monad m => MonadState BackTrackState (BackT m) where
  get = StLaz.get
  put = StLaz.put

btFresh :: Monad m => BackT m Int
btFresh = do
  i <- get
  put $ i+1
  return i

btBind :: Monad m => Int -> Int -> BackT m ()
btBind k v = modify ((k,v):)
-}

main = do
  -- forM_ (queens1 8) print
  -- forM_ (queens2 8) print
  -- forM_ (observeAll () $ queens1L 8) print
  -- forM_ (observeAll () $ (queens2L 8 :: Logic [Int])) print
  -- forM_ (observeAll (0::Int,0::Int) $ (queens3L 8 :: LogicVar Int Int ((Int,Int),[Int]))) print
  -- forM_ (observeMany (0::Int,0::Int) 5000 $ (queens3L 10 :: LogicState Int Int ((Int,Int),[Int]))) print
  -- forM_ (observe (0::Int,0::Int) $ (queens3L 8 :: LogicVar Int Int ((Int,Int),[Int]))) print
  -- forM_ (stepwiseEval $ queens4S 8) print
  E.main
