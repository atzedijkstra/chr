-------------------------------------------------------------------------
-- Wrapper module around Data.Binary, providing additional functionality
-------------------------------------------------------------------------

module UHC.Util.Binary
  ( module Data.Binary
  , module Data.Binary.Get
  , module Data.Binary.Put
  , module UHC.Util.Control.Monad
  , module Data.Typeable
  -- , module Data.Generics

  , hGetBinary
  , getBinaryFile
  , getBinaryFPath

  , hPutBinary
  , putBinaryFile
  , putBinaryFPath

  , putEnum, getEnum
  , putEnum8, getEnum8
  -- , putList, getList
  )
  where

import qualified Data.ByteString.Lazy as L
import Data.Typeable
-- import Data.Generics (Data)
import Data.Binary
import Data.Binary.Put(runPut,putWord16be)
import Data.Binary.Get(runGet,getWord16be)
import System.IO
import Control.Monad
import UHC.Util.Control.Monad

{-
import Data.Generics.Aliases
import Data.Word
import Data.Array
import Control.Monad
-}

import UHC.Util.FPath

-------------------------------------------------------------------------
-- Decoding from ...
-------------------------------------------------------------------------

-- | Decode from Handle
hGetBinary :: Binary a => Handle -> IO a
hGetBinary h
  = liftM decode (L.hGetContents h)

-- | Decode from FilePath
getBinaryFile :: Binary a => FilePath -> IO a
getBinaryFile fn
  = do { h <- openBinaryFile fn ReadMode
       ; b <- hGetBinary h
       -- ; hClose h
       ; return b ;
       }

-- | Decode from FilePath
getBinaryFPath :: Binary a => FPath -> IO a
getBinaryFPath fp
  = getBinaryFile (fpathToStr fp)

-------------------------------------------------------------------------
-- Encoding to ...
-------------------------------------------------------------------------

-- | Encode to Handle
hPutBinary :: Binary a => Handle -> a -> IO ()
hPutBinary h pt
  = L.hPut h (encode pt)

-- | Encode to FilePath
putBinaryFile :: Binary a => FilePath -> a -> IO ()
putBinaryFile fn pt
  = do { h <- openBinaryFile fn WriteMode
       ; hPutBinary h pt
       ; hClose h
       }

-- | Encode to FPath, ensuring existence of path
putBinaryFPath :: Binary a => FPath -> a -> IO ()
putBinaryFPath fp pt
  = do { fpathEnsureExists fp
       ; putBinaryFile (fpathToStr fp) pt
       }

-------------------------------------------------------------------------
-- Enum based put/get
-------------------------------------------------------------------------

-- | put an Enum
putEnum :: Enum x => x -> Put
putEnum x = put (fromEnum x)

-- | get an Enum
getEnum :: Enum x => Get x
getEnum = do n <- get
             return (toEnum n)


-- | put an Enum as Word8
putEnum8 :: Enum x => x -> Put
putEnum8 x = putWord8 (fromIntegral $ fromEnum x)

-- | get an Enum from Word8
getEnum8 :: Enum x => Get x
getEnum8 = do n <- getWord8
              return (toEnum $ fromIntegral n)

{-
-- | put a []
putList :: (Binary a, Binary b) => (x -> Bool) -> (x -> (a,b)) -> x -> Put
putList isNil getCons x | isNil x   = putWord8 0
                        | otherwise = let (a,b) = getCons x in putWord8 1 >> put a >> put b

-- | get a []
getList :: (Binary a, Binary b) => x -> (a -> b -> x) -> Get x
getList nil cons
  = do tag <- getWord8
       case tag of
         0 -> return nil
         1 -> liftM2 cons get get
-}
