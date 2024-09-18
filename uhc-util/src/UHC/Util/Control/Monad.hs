{- |
Extensions to Control.Monad
-}

module UHC.Util.Control.Monad
  ( liftM6
  , liftM7
  , liftM8
  , liftM9
  )
  where

liftM6  :: (Monad m) => (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> r)
           -> m a1 -> m a2 -> m a3 -> m a4 -> m a5 -> m a6 -> m r
liftM6 f m1 m2 m3 m4 m5 m6
  = do { x1 <- m1; x2 <- m2; x3 <- m3; x4 <- m4; x5 <- m5; x6 <- m6
       ; return (f x1 x2 x3 x4 x5 x6)
       }

liftM7  :: (Monad m) => (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> r)
           -> m a1 -> m a2 -> m a3 -> m a4 -> m a5 -> m a6 -> m a7 -> m r
liftM7 f m1 m2 m3 m4 m5 m6 m7
  = do { x1 <- m1; x2 <- m2; x3 <- m3; x4 <- m4; x5 <- m5; x6 <- m6; x7 <- m7
       ; return (f x1 x2 x3 x4 x5 x6 x7)
       }

liftM8  :: (Monad m) => (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> r)
           -> m a1 -> m a2 -> m a3 -> m a4 -> m a5 -> m a6 -> m a7 -> m a8 -> m r
liftM8 f m1 m2 m3 m4 m5 m6 m7 m8
  = do { x1 <- m1; x2 <- m2; x3 <- m3; x4 <- m4; x5 <- m5; x6 <- m6; x7 <- m7; x8 <- m8
       ; return (f x1 x2 x3 x4 x5 x6 x7 x8)
       }

liftM9  :: (Monad m) => (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> r)
           -> m a1 -> m a2 -> m a3 -> m a4 -> m a5 -> m a6 -> m a7 -> m a8 -> m a9 -> m r
liftM9 f m1 m2 m3 m4 m5 m6 m7 m8 m9
  = do { x1 <- m1; x2 <- m2; x3 <- m3; x4 <- m4; x5 <- m5; x6 <- m6; x7 <- m7; x8 <- m8; x9 <- m9
       ; return (f x1 x2 x3 x4 x5 x6 x7 x8 x9)
       }
