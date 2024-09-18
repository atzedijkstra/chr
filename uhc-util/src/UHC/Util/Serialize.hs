{-
Serialization is built on top of Binary, adding sharing, additionally
requiring Typeable and Ord instances for maintaining maps. Whilst
putting/getting a map is maintained which remembers previously put
values. When such a value is put a 2nd time, a reference to it is put
instead.

Values which are shared, put share commands (SCmd) onto the Binary
serialization. There are SCmds for defining a shared value and referring
to it, coming in 8/16/.. bitsized reference flavors (this saves space).

Turning on serialization means defining an instance for the type of the
value, similar to instances for Binary:

\begin{code}
data Foo = Bar1 | Bar2 Int Int

instance Serialize Foo where
  sput (Bar1    ) = sputWord8 0
  sput (Bar2 a b) = sputWord8 1 >> sput a >> sput b
  sget
    = do t <- sgetWord8
         case t of
           0 -> return Bar1
           1 -> liftM2 Bar2 sget sget
\end{code}

When a Binary instance already is defined, the definition can be more simple:
\begin{code}
instance Serialize Foo where
  sput = sputPlain
  sget = sgetPlain
\end{code}

The plain variants delegate the work to their Binary equivalents.

By default no sharing is done, it can be enabled by:

\begin{code}
instance Serialize Foo where
  sput = sputShared
  sget = sgetShared
  sputNested = sputPlain
  sgetNested = sgetPlain
\end{code}

When shared the internals are not shared, as above. If the internals
(i.e. the fields) also must be shared the following instance is
required, using the original code for sput/sget for the fields of a
value:

\begin{code}
instance Serialize Foo where
  sput = sputShared
  sget = sgetShared
  sputNested (Bar1    ) = sputWord8 0
  sputNested (Bar2 a b) = sputWord8 1 >> sput a >> sput b
  sgetNested
    = do t <- sgetWord8
         case t of
           0 -> return Bar1
           1 -> liftM2 Bar2 sget sget
\end{code}


-}

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

-- for generics
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module UHC.Util.Serialize
    ( SPut
    , SGet
    , Serialize (..)
    , sputPlain, sgetPlain
    , sputUnshared, sputShared
    , sgetShared
    , sputWord8, sgetWord8
    , sputWord16, sgetWord16
    , sputEnum8, sgetEnum8
    , runSPut, runSGet
    , serialize, unserialize
    , putSPutFile, getSGetFile
    , putSerializeFile, getSerializeFile
    , Generic
    )
  where
import qualified UHC.Util.Binary as Bn
import qualified Data.ByteString.Lazy as L
import           System.IO
import           System.IO (openBinaryFile)
import           UHC.Util.Utils
import           Data.Typeable
-- import           Data.Typeable.Internal
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List
-- import qualified UHC.Utils.RelMap as RelMap
import           Data.Maybe
import           Data.Bits
import           Data.Word
import           Data.Int
import           Data.Array
import           Control.Monad
import qualified Control.Monad.State as St
import           Control.Monad.Trans

-- for generics
import           GHC.Generics
import           Control.Applicative

{- | Serialization with state.
Shared values are stored in a per type map, to keep all type correct. To
make this work a double mapping is maintained, keyed by the type
descriptor string of a type (obtained via Typeable) and keyed by the Int
reference to it.
-}
data SCmd
  = SCmd_Unshared
  | SCmd_ShareDef   | SCmd_ShareRef         --
  | SCmd_ShareDef16 | SCmd_ShareRef16
  | SCmd_ShareDef8  | SCmd_ShareRef8
  deriving (Enum)

instance Bn.Binary SCmd where
  put = Bn.putEnum8
  get = Bn.getEnum8

scmdTo16 :: SCmd -> SCmd
scmdTo16 SCmd_ShareDef = SCmd_ShareDef16
scmdTo16 SCmd_ShareRef = SCmd_ShareRef16
scmdTo16 c             = c

scmdTo8 :: SCmd -> SCmd
scmdTo8 SCmd_ShareDef = SCmd_ShareDef8
scmdTo8 SCmd_ShareRef = SCmd_ShareRef8
scmdTo8 c             = c

scmdToNrBits :: SCmd -> Int
scmdToNrBits SCmd_ShareDef16 = 16
scmdToNrBits SCmd_ShareRef16 = 16
scmdToNrBits SCmd_ShareDef8  = 8
scmdToNrBits SCmd_ShareRef8  = 8
scmdToNrBits _               = 32

scmdFrom :: SCmd -> SCmd
scmdFrom SCmd_ShareDef16 = SCmd_ShareDef
scmdFrom SCmd_ShareRef16 = SCmd_ShareRef
scmdFrom SCmd_ShareDef8  = SCmd_ShareDef
scmdFrom SCmd_ShareRef8  = SCmd_ShareRef
scmdFrom c               = c

data SerPutMp = forall x . (Typeable x, Ord x) => SerPutMp (Map.Map x Int)

data SPutS
  = SPutS
      { sputsInx :: Int
      , sputsSMp :: Map.Map String SerPutMp
      , sputsPut :: Bn.Put
      }

emptySPutS = SPutS 0 Map.empty (return ())

type SPut = St.State SPutS ()


data SerGetMp = forall x . (Typeable x, Ord x) => SerGetMp (Map.Map Int x)

data SGetS
  = SGetS
      { sgetsSMp :: Map.Map String SerGetMp
      }

type SGet x = St.StateT SGetS Bn.Get x

class Serialize x where
  sput :: x -> SPut
  default sput :: (Generic x, GSerialize (Rep x)) => x -> SPut
  sput = gsput . from

  sget :: SGet x
  default sget :: (Generic x, GSerialize (Rep x)) => SGet x
  sget = to <$> gsget

  sputNested :: x -> SPut
  sgetNested :: SGet x

  -- default just falls back on Binary, invoked by sputShared/sgetShared
  sputNested = panic "not implemented (must be done by instance): Serialize.sputNested"
  sgetNested = panic "not implemented (must be done by instance): Serialize.sgetNested"


liftP :: Bn.Put -> SPut
liftP p
  = do { s <- St.get
       ; St.put (s { sputsPut = sputsPut s >> p
                   })
       }
{-# INLINE liftP #-}

liftG :: Bn.Get x -> SGet x
liftG g = lift g
{-# INLINE liftG #-}

sputPlain :: (Bn.Binary x,Serialize x) => x -> SPut
sputPlain x = liftP (Bn.put x)
{-# INLINE sputPlain #-}

sgetPlain :: (Bn.Binary x,Serialize x) => SGet x
sgetPlain = lift Bn.get
{-# INLINE sgetPlain #-}


sputUnshared :: (Bn.Binary x,Serialize x) => x -> SPut
sputUnshared x
  = do { s <- St.get
       ; St.put (s { sputsPut = sputsPut s >> Bn.put SCmd_Unshared >> Bn.put x
                   })
       }

putRef :: SCmd -> Int -> Bn.Put
putRef c i
  = if i < 256
    then do { Bn.put (scmdTo8 c)
            ; Bn.putWord8 (fromIntegral i)
            }
    else if i < 65000
    then do { Bn.put (scmdTo16 c)
            ; Bn.putWord16be (fromIntegral i)
            }
    else do { Bn.put c
            ; Bn.put i
            }

sputShared :: (Ord x, Serialize x, Typeable x) => x -> SPut
sputShared x
  = do { s <- St.get
       ; let tykey = tyConName $ typeRepTyCon $ typeOf x
       ; case Map.lookup tykey (sputsSMp s) of
           Just (SerPutMp m)
             -> case Map.lookup xcasted m of
                  Just i
                    -> useExisting i s
                  _ -> addNew tykey x xcasted m s
             where xcasted = panicJust "Serialize.sputShared A" $ cast x
           _ -> addNew tykey x x Map.empty s
       }
  where useExisting i s
          = St.put (s { sputsPut = sputsPut s >> putRef SCmd_ShareRef i })
        addNew tykey x xcasted m s
          = do { St.put (s { sputsInx = i+1
                           , sputsSMp = Map.insert tykey (SerPutMp (Map.insert xcasted i m)) (sputsSMp s)
                           , sputsPut = sputsPut s >> putRef SCmd_ShareDef i
                           })
               ; sputNested x
               }
          where i = sputsInx s

getRef :: SCmd -> Bn.Get Int
getRef c
  = case scmdToNrBits c of
      8 -> do { i <- Bn.getWord8
              ; return (fromIntegral i :: Int)
              }
      16-> do { i <- Bn.getWord16be
              ; return (fromIntegral i :: Int)
              }
      _ -> Bn.get

sgetShared :: forall x. (Ord x, Serialize x, Typeable x) => SGet x
sgetShared
  = do { cmd <- lift Bn.get
       ; case scmdFrom cmd of
           SCmd_Unshared
             -> sgetNested
           SCmd_ShareDef
             -> do { i <- lift (getRef cmd)
                   ; x <- sgetNested
                   ; s <- St.get
                   ; let tykey = tyConName $ typeRepTyCon $ typeOf (undefined :: x)
                   ; case Map.lookup tykey (sgetsSMp s) of
                       Just (SerGetMp m)
                         -> St.put (s { sgetsSMp = Map.insert tykey (SerGetMp (Map.insert i xcasted m)) (sgetsSMp s)
                                      })
                         where xcasted = panicJust "Serialize.sgetShared A" $ cast x
                       _ -> St.put (s { sgetsSMp = Map.insert tykey (SerGetMp (Map.singleton i x)) (sgetsSMp s)
                                      })
                   ; return x
                   }
           SCmd_ShareRef
             -> do { i <- lift (getRef cmd)
                   ; s <- St.get
                   ; let tykey = tyConName $ typeRepTyCon $ typeOf (undefined :: x)
                   ; case Map.lookup tykey (sgetsSMp s) of
                       Just (SerGetMp m)
                         -> return $ panicJust "Serialize.sgetShared C" $ cast $ panicJust "Serialize.sgetShared B" $ Map.lookup i m
                       _ -> panic "Serialize.sgetShared D"
                   }
       }


-- Low level

sputWord8            :: Word8 -> SPut
sputWord8 x          = liftP (Bn.putWord8 x)
{-# INLINE sputWord8 #-}

sgetWord8 :: SGet Word8
sgetWord8 = liftG Bn.getWord8
{-# INLINE sgetWord8 #-}


sputWord16           :: Word16 -> SPut
sputWord16 x         = liftP (Bn.putWord16be x)
{-# INLINE sputWord16 #-}

sgetWord16 :: SGet Word16
sgetWord16 = liftG Bn.getWord16be
{-# INLINE sgetWord16 #-}


sputEnum8 :: Enum x => x -> SPut
sputEnum8 x = liftP (Bn.putEnum8 x)
{-# INLINE sputEnum8 #-}

sgetEnum8 :: Enum x => SGet x
sgetEnum8 = liftG Bn.getEnum8
{-# INLINE sgetEnum8 #-}

-- Default instances, copied & modified from Binary

instance Serialize () where
  sput _ = return ()
  sget   = return ()

instance Serialize Int where
  sput = sputPlain
  sget = sgetPlain

instance Serialize Char where
  sput = sputPlain
  sget = sgetPlain

instance Serialize Bool where
  sput = sputPlain
  sget = sgetPlain

instance Serialize Integer where
  sput = sputPlain
  sget = sgetPlain

instance Serialize Word64 where
  sput = sputPlain
  sget = sgetPlain

instance Serialize Int64 where
  sput = sputPlain
  sget = sgetPlain

instance Serialize Word32 where
  sput = sputPlain
  sget = sgetPlain

instance Serialize Int32 where
  sput = sputPlain
  sget = sgetPlain

instance Serialize Word16 where
  sput = sputPlain
  sget = sgetPlain

instance Serialize Int16 where
  sput = sputPlain
  sget = sgetPlain

{- FIXME? TypeRep changed, this does not work anymore...
instance Serialize TyCon where
  sput tc = sput (tyConPackage tc) >> sput (tyConModule tc) >> sput (tyConName tc)
  sget = liftM3 mkTyCon3 sget sget sget

instance Serialize TypeRep where
  sput tr = sput tc >> sput ka >> sput ta
    where (tc,ka,ta) = splitPolyTyConApp tr
  sget = liftM3 mkPolyTyConApp sget sget sget
-}  
  
  
{-
instance Serialize String where
  sput = sputShared
  sget = sgetShared
  sputNested = sputPlain
  sgetNested = sgetPlain
-}

instance (Serialize a, Serialize b) => Serialize (a,b) where
    -- sput (a,b)           = sput a >> sput b
    -- sget                 = liftM2 (,) sget sget

instance (Serialize a, Serialize b, Serialize c) => Serialize (a,b,c) where
    -- sput (a,b,c)         = sput a >> sput b >> sput c
    -- sget                 = liftM3 (,,) sget sget sget

instance Serialize a => Serialize [a] where
    sput l  = sput (length l) >> mapM_ sput l
    sget    = do n <- sget :: SGet Int
                 replicateM n sget

instance (Serialize a) => Serialize (Maybe a) where
    -- sput Nothing  = sputWord8 0
    -- sput (Just x) = sputWord8 1 >> sput x
    -- sget = do
    --     w <- sgetWord8
    --     case w of
    --         0 -> return Nothing
    --         _ -> liftM Just sget

instance (Ord a, Serialize a) => Serialize (Set.Set a) where
    sput = sput . Set.toAscList
    sget = liftM Set.fromDistinctAscList sget

instance (Ord k, Serialize k, Serialize e) => Serialize (Map.Map k e) where
    sput = sput . Map.toAscList
    sget = liftM Map.fromDistinctAscList sget

-- The actual IO

runSPut :: SPut -> Bn.Put
runSPut x = sputsPut $ St.execState x emptySPutS

runSGet :: SGet x -> Bn.Get x
runSGet x = St.evalStateT x (SGetS Map.empty)


serialize :: Serialize x => x -> Bn.Put
serialize x = runSPut (sput x)

unserialize :: Serialize x => Bn.Get x
unserialize = runSGet sget


-- | SPut to FilePath
putSPutFile :: FilePath -> SPut -> IO ()
putSPutFile fn x
  = do { h <- openBinaryFile fn WriteMode
       ; L.hPut h (Bn.runPut $ runSPut x)
       ; hClose h
       }

-- | SGet from FilePath
getSGetFile :: FilePath -> SGet a -> IO a
getSGetFile fn x
  = do { h <- openBinaryFile fn ReadMode
       ; s <- L.hGetContents h
       ; b <- L.length s `seq` (return $ Bn.runGet (runSGet x) s)
       ; hClose h
       ; return b ;
       }

-- | Serialize to FilePath
putSerializeFile :: Serialize a => FilePath -> a -> IO ()
putSerializeFile fn x
  = do { h <- openBinaryFile fn WriteMode
       ; L.hPut h (Bn.runPut $ serialize x)
       ; hClose h
       }

-- | Unserialize from FilePath
getSerializeFile :: Serialize a => FilePath -> IO a
getSerializeFile fn
  = do { h <- openBinaryFile fn ReadMode
       ; s <- L.hGetContents h
       ; b <- L.length s `seq` (return $ Bn.runGet unserialize s)
       ; hClose h
       ; return b ;
       }

-- generic serialize

class GSerialize x where
  gsget :: SGet (x y)
  gsput :: x y -> SPut

instance (Datatype d, SerializeSumTagged x) => GSerialize (D1 d x) where
  --
  gsget = do 
    tg <- sgetWord8
    M1 <$> sumGetTagged tg
  --
  gsput (M1 x) = sumPutTagged [] x

class SerializeSumTagged x where
  sumGetTagged :: Word8 -> SGet (x y)
  sumPutTagged :: [Word8] -> x y -> SPut

instance (SerializeProduct x) => SerializeSumTagged (C1 c x) where
  --
  sumGetTagged _ = M1 <$> productGet
  {-# INLINE sumGetTagged #-}
  --
  sumPutTagged tg (M1 x) = sputWord8 (List.foldl' (\acc t -> (acc `shiftL` 1) .|. t) 0 tg) >> productPut x
  {-# INLINE sumPutTagged #-}

instance (SerializeSumTagged a, SerializeSumTagged b) => SerializeSumTagged (a :+: b) where
  sumGetTagged tg = 
      if tg `testBit` 0
        then L1 <$> sumGetTagged tg'
        else R1 <$> sumGetTagged tg'
    where tg' = tg `shiftR` 1
  {-# INLINE sumGetTagged #-}

  sumPutTagged tg x = case x of
      L1 x' -> sumPutTagged (1:tg) x'
      R1 x' -> sumPutTagged (0:tg) x'
  {-# INLINE sumPutTagged #-}

class SerializeProduct x where
  productGet :: SGet (x y)
  productPut :: x y -> SPut

instance (SerializeProduct a, SerializeProduct b) => SerializeProduct (a :*: b) where
  productGet =
      (:*:) <$> productGet
            <*> productGet
  {-# INLINE productGet #-}

  productPut (a :*: b) = do
      productPut a
      productPut b
  {-# INLINE productPut #-}

instance SerializeProduct x => SerializeProduct (S1 s x) where
  productGet = M1 <$> productGet
  {-# INLINE productGet #-}

  productPut (M1 x) = productPut x
  {-# INLINE productPut #-}

instance Serialize x => SerializeProduct (K1 i x) where
  productGet = K1 <$> sget
  {-# INLINE productGet #-}

  productPut (K1 x) = sput x
  {-# INLINE productPut #-}

instance SerializeProduct U1 where
  productGet = return U1
  {-# INLINE productGet #-}
  productPut _ = return ()
  {-# INLINE productPut #-}
