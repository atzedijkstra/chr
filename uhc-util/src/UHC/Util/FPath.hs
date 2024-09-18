{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

{-| Library for manipulating a more structured version of FilePath.
    Note: the library should use System.FilePath functionality but does not do so yet.
 -}

module UHC.Util.FPath
  ( 
  -- * FPath datatype, FPATH class for overloaded construction
    FPath(..), fpathSuff
  , FPATH(..)
  , FPathError -- (..) -- can be removed...
  , emptyFPath
  
  -- * Construction, deconstruction, predicates
  -- , mkFPath
  , fpathFromStr
  , mkFPathFromDirsFile
  , fpathToStr, fpathIsEmpty
  , fpathSetBase, fpathSetSuff, fpathSetDir
  , fpathUpdBase
  , fpathRemoveSuff, fpathRemoveDir

  , fpathIsAbsolute

  , fpathAppendDir, fpathUnAppendDir
  , fpathPrependDir, fpathUnPrependDir
  , fpathSplitDirBy
  , mkTopLevelFPath

  -- * SearchPath
  , SearchPath
  , FileSuffixes, FileSuffixesWith
  , FileSuffix, FileSuffixWith
  , mkInitSearchPath, searchPathFromFPath, searchPathFromFPaths
  , searchPathFromString
  , searchFPathFromLoc
  , searchLocationsForReadableFilesWith
  , searchLocationsForReadableFiles
  , searchPathForReadableFiles
  , searchPathForReadableFile

  , fpathEnsureExists

  -- * Path as prefix
  , filePathMkPrefix, filePathUnPrefix
  , filePathCoalesceSeparator
  , filePathMkAbsolute, filePathUnAbsolute
  
  -- * Misc
  , fpathGetModificationTime

  , fpathDirSep, fpathDirSepChar

  , fpathOpenOrStdin, openFPath

  )
where

import Data.Maybe
import Data.Typeable
import Data.List
import Control.Monad
import System.IO
import System.Directory

import GHC.Generics

import UHC.Util.Utils
import UHC.Util.Time

-------------------------------------------------------------------------------------------
-- Making prefix and inverse, where a prefix has a tailing '/'
-------------------------------------------------------------------------------------------

-- | Construct a filepath to be a prefix (i.e. ending with '/' as last char)
filePathMkPrefix :: FilePath -> FilePath
filePathMkPrefix d@(_:_) | last d /= '/'    = d ++ "/"
filePathMkPrefix d                          = d

-- | Remove from a filepath a possibly present '/' as last char
filePathUnPrefix :: FilePath -> FilePath
filePathUnPrefix d | isJust il && l == '/'  = filePathUnPrefix i
  where il = initlast d
        (i,l) = fromJust il
filePathUnPrefix d                          = d

-- | Remove consecutive occurrences of '/'
filePathCoalesceSeparator :: FilePath -> FilePath
filePathCoalesceSeparator ('/':d@('/':_)) = filePathCoalesceSeparator d
filePathCoalesceSeparator (c:d) = c : filePathCoalesceSeparator d
filePathCoalesceSeparator d     = d

-------------------------------------------------------------------------------------------
-- Making into absolute path and inverse, where absolute means a heading '/'
-------------------------------------------------------------------------------------------

-- | Make a filepath an absolute filepath by prefixing with '/'
filePathMkAbsolute :: FilePath -> FilePath
filePathMkAbsolute d@('/':_ ) = d
filePathMkAbsolute d          = "/" ++ d

-- | Make a filepath an relative filepath by removing prefixed '/'-s
filePathUnAbsolute :: FilePath -> FilePath
filePathUnAbsolute d@('/':d') = filePathUnAbsolute d'
filePathUnAbsolute d          = d

-------------------------------------------------------------------------------------------
-- File path
-------------------------------------------------------------------------------------------

-- | File path representation making explicit (possible) directory, base and (possible) suffix
data FPath
  = FPath
      { fpathMbDir      :: !(Maybe  FilePath)
      , fpathBase       ::         !String
      , fpathMbSuff     :: !(Maybe  String)
      }
    deriving (Show,Eq,Ord,Typeable,Generic)

-- | Empty FPath
emptyFPath :: FPath
emptyFPath
  = mkFPath ""

-- | Is FPath empty?
fpathIsEmpty :: FPath -> Bool
fpathIsEmpty fp = null (fpathBase fp)

-- | Conversion to FilePath
fpathToStr :: FPath -> FilePath
fpathToStr fpath
  = let adds f = maybe f (\s -> f ++ "."         ++ s) (fpathMbSuff fpath)
        addd f = maybe f (\d -> d ++ fpathDirSep ++ f) (fpathMbDir fpath)
     in addd . adds . fpathBase $ fpath

-------------------------------------------------------------------------------------------
-- Observations
-------------------------------------------------------------------------------------------

-- TBD. does not work under WinXX, use FilePath library
fpathIsAbsolute :: FPath -> Bool
fpathIsAbsolute fp
  = case fpathMbDir fp of
      Just ('/':_) -> True
      _            -> False

-------------------------------------------------------------------------------------------
-- Utilities, (de)construction
-------------------------------------------------------------------------------------------

-- | Construct FPath from FilePath
fpathFromStr :: FilePath -> FPath
fpathFromStr fn
  = FPath d b' s
  where (d ,b) = maybe (Nothing,fn) (\(d,b) -> (Just d,b)) (splitOnLast fpathDirSepChar fn)
        (b',s) = maybe (b,Nothing)  (\(b,s) -> (b,Just s)) (splitOnLast '.'             b )

-- | Construct FPath directory from FilePath
fpathDirFromStr :: String -> FPath
fpathDirFromStr d = emptyFPath {fpathMbDir = Just d}
{-# INLINE fpathDirFromStr #-}

-- | Get suffix, being empty equals the empty String
fpathSuff :: FPath -> String
fpathSuff = maybe "" id . fpathMbSuff

-- | Set the base
fpathSetBase :: String -> FPath -> FPath
fpathSetBase s fp
  = fp {fpathBase = s}
{-# INLINE fpathSetBase #-}

-- | Modify the base
fpathUpdBase :: (String -> String) -> FPath -> FPath
fpathUpdBase u fp
  = fp {fpathBase = u (fpathBase fp)}
{-# INLINE fpathUpdBase #-}

-- | Set suffix, empty String removes it
fpathSetSuff :: String -> FPath -> FPath
fpathSetSuff "" fp
  = fpathRemoveSuff fp
fpathSetSuff s fp
  = fp {fpathMbSuff = Just s}

-- | Set suffix, empty String leaves old suffix
fpathSetNonEmptySuff :: String -> FPath -> FPath
fpathSetNonEmptySuff "" fp
  = fp
fpathSetNonEmptySuff s fp
  = fp {fpathMbSuff = Just s}

-- | Set directory, empty FilePath removes it
fpathSetDir :: FilePath -> FPath -> FPath
fpathSetDir "" fp
  = fpathRemoveDir fp
fpathSetDir d fp
  = fp {fpathMbDir = Just d}

-- | Split FPath into given directory (prefix) and remainder, fails if not a prefix
fpathSplitDirBy :: FilePath -> FPath -> Maybe (String,String)
fpathSplitDirBy byDir fp
  = do { d      <- fpathMbDir fp
       ; dstrip <- stripPrefix byDir' d
       ; return (byDir',filePathUnAbsolute dstrip)
       }
  where byDir' = filePathUnPrefix byDir

-- | Prepend directory
fpathPrependDir :: FilePath -> FPath -> FPath
fpathPrependDir "" fp
  = fp
fpathPrependDir d fp
  = maybe (fpathSetDir d fp) (\fd -> fpathSetDir (d ++ fpathDirSep ++ fd) fp) (fpathMbDir fp)

-- | Remove directory (prefix), using 'fpathSplitDirBy'
fpathUnPrependDir :: FilePath -> FPath -> FPath
fpathUnPrependDir d fp
  = case fpathSplitDirBy d fp of
      Just (_,d) -> fpathSetDir d fp
      _          -> fp

-- | Append directory (to directory part)
fpathAppendDir :: FPath -> FilePath -> FPath
fpathAppendDir fp ""
  = fp
fpathAppendDir fp d
  = maybe (fpathSetDir d fp) (\fd -> fpathSetDir (fd ++ fpathDirSep ++ d) fp) (fpathMbDir fp)

-- | Remove common trailing part of dir.
-- Note: does not check whether it really is a suffix.
fpathUnAppendDir :: FPath -> FilePath -> FPath
fpathUnAppendDir fp ""
  = fp
fpathUnAppendDir fp d
  = case fpathMbDir fp of
      Just p -> fpathSetDir (filePathUnPrefix prefix) fp
             where (prefix,_) = splitAt (length p - length d) p
      _      -> fp

-- | Remove suffix
fpathRemoveSuff :: FPath -> FPath
fpathRemoveSuff fp
  = fp {fpathMbSuff = Nothing}
{-# INLINE fpathRemoveSuff #-}

-- | Remove dir
fpathRemoveDir :: FPath -> FPath
fpathRemoveDir fp
  = fp {fpathMbDir = Nothing}
{-# INLINE fpathRemoveDir #-}

mkFPathFromDirsFile :: Show s => [s] -> s -> FPath
mkFPathFromDirsFile dirs f
  = fpathSetDir (concat $ intersperse fpathDirSep $ map show $ dirs) (mkFPath (show f))

-- | Make FPath from FilePath, setting the suffix when absent
mkTopLevelFPath
  :: String     -- ^ suffix
  -> FilePath   -- ^ file name
  -> FPath
mkTopLevelFPath suff fn
  = let fpNoSuff = mkFPath fn
     in maybe (fpathSetSuff suff fpNoSuff) (const fpNoSuff) $ fpathMbSuff fpNoSuff

-------------------------------------------------------------------------------------------
-- Utils
-------------------------------------------------------------------------------------------

splitOnLast :: Char -> String -> Maybe (String,String)
splitOnLast splitch fn
  = case fn of
      ""     -> Nothing
      (f:fs) -> let rem = splitOnLast splitch fs
                 in if f == splitch
                    then maybe (Just ("",fs)) (\(p,s)->Just (f:p,s)) rem
                    else maybe Nothing (\(p,s)->Just (f:p,s)) rem

-------------------------------------------------------------------------------------------
-- Config, should be dealt with by FilePath utils
-------------------------------------------------------------------------------------------

fpathDirSep :: String
fpathDirSep = "/"
{-# INLINE fpathDirSep #-}

fpathDirSepChar :: Char
fpathDirSepChar = head fpathDirSep
{-# INLINE fpathDirSepChar #-}

-------------------------------------------------------------------------------------------
-- Class 'can make FPath of ...'
-------------------------------------------------------------------------------------------

-- | Construct a FPath from some type
class FPATH f where
  mkFPath :: f -> FPath

instance FPATH String where
  mkFPath = fpathFromStr

instance FPATH FPath where
  mkFPath = id

-------------------------------------------------------------------------------------------
-- Class 'is error related to FPath'
-------------------------------------------------------------------------------------------

-- | Is error related to FPath
class FPathError e

instance FPathError String

-------------------------------------------------------------------------------------------
-- Open path for read or return stdin
-------------------------------------------------------------------------------------------

fpathOpenOrStdin :: FPath -> IO (FPath,Handle)
fpathOpenOrStdin fp
  = if fpathIsEmpty fp
    then return (mkFPath "<stdin>",stdin)
    else do { let fn = fpathToStr fp
            ; h <- openFile fn ReadMode
            ; return (fp,h)
            }

openFPath :: FPath -> IOMode -> Bool -> IO (String, Handle)
openFPath fp mode binary
  | fpathIsEmpty fp = case mode of
                        ReadMode      -> return ("<stdin>" ,stdin )
                        WriteMode     -> return ("<stdout>",stdout)
                        AppendMode    -> return ("<stdout>",stdout)
                        ReadWriteMode -> error "cannot use stdin/stdout with random access"
  | otherwise       = do { let fNm = fpathToStr fp
                         ; h <- if binary
                                then openBinaryFile fNm mode
                                else openFile fNm mode
                         ; return (fNm,h)
                         }

-------------------------------------------------------------------------------------------
-- Directory
-------------------------------------------------------------------------------------------

fpathEnsureExists :: FPath -> IO ()
fpathEnsureExists fp
  = do { let d = fpathMbDir fp
       ; when (isJust d) (createDirectoryIfMissing True (fromJust d))
       }

-------------------------------------------------------------------------------------------
-- Search path utils
-------------------------------------------------------------------------------------------

type SearchPath = [String]
type FileSuffix   =  Maybe String
-- | FileSuffix with extra payload
type FileSuffixWith x =  (Maybe String, x)
type FileSuffixes = [FileSuffix]
-- | FileSuffix with extra payload
type FileSuffixesWith x = [FileSuffixWith x]

searchPathFromFPaths :: [FPath] -> SearchPath
searchPathFromFPaths fpL = nub [ d | (Just d) <- map fpathMbDir fpL ] ++ [""]

searchPathFromFPath :: FPath -> SearchPath
searchPathFromFPath fp = searchPathFromFPaths [fp]
{-# INLINE searchPathFromFPath #-}

mkInitSearchPath :: FPath -> SearchPath
mkInitSearchPath = searchPathFromFPath
{-# INLINE mkInitSearchPath #-}

searchPathFromString :: String -> [String]
searchPathFromString
  = unfoldr f
  where f "" = Nothing
        f sp = Just (break (== ';') sp)

-- Simple function that returns a particular file under a
-- certain root dir.
searchFPathFromLoc :: FilePath -> FPath -> [(FilePath,FPath)]
searchFPathFromLoc loc fp = [(loc,fpathPrependDir loc fp)]

-- | Search for file in locations, with possible suffices
searchLocationsForReadableFilesWith
  ::    (loc -> FPath -> [(loc,FPath,[e])])             -- ^ get the locations for a name, possibly with errors
     -> Bool                                            -- ^ stop when first is found
     -> [loc]                                           -- ^ locations to search
     -> FileSuffixesWith s                              -- ^ suffixes to try, with associated info
     -> FPath                                           -- ^ search for a path
     -> IO [(FPath,loc,s,[e])]
searchLocationsForReadableFilesWith getfp stopAtFirst locs suffs fp
  = let select stop f fps
          = foldM chk [] fps
          where chk r fp
                  = case r of
                      (_:_) | stop -> return r
                      _            -> do r' <- f fp
                                         return (r ++ r')
        tryToOpen loc (mbSuff,suffinfo) fp
          = do { let fp' = maybe fp (\suff -> fpathSetNonEmptySuff suff fp) mbSuff
               ; fExists <- doesFileExist (fpathToStr fp')
               -- ; hPutStrLn stderr (show fp ++ " - " ++ show fp')
               ; if fExists
                 then return [(fp',loc,suffinfo)]
                 else return []
               }
        tryToOpenWithSuffs suffs (loc,fp,x)
          = fmap (map (tup123to1234 x)) $
            case suffs of
              [] -> tryToOpen loc (Nothing,panic "searchLocationsForReadableFilesWith.tryToOpenWithSuffs.tryToOpen") fp
              _  -> select stopAtFirst
                      (\(ms,f) -> tryToOpen loc ms f)
                      ({- (Nothing,fp) : -} zip suffs (repeat fp))
        tryToOpenInDir loc
          = select True (tryToOpenWithSuffs suffs) (getfp loc fp)
     in select True tryToOpenInDir locs

-- | Search for file in locations, with possible suffices
searchLocationsForReadableFiles
  ::    (loc -> FPath -> [(loc,FPath,[e])])             -- ^ get the locations for a name, possibly with errors
     -> Bool                                            -- ^ stop when first is found
     -> [loc]                                           -- ^ locations to search
     -> FileSuffixes                                    -- ^ suffixes to try
     -> FPath                                           -- ^ search for a path
     -> IO [(FPath,loc,[e])]
searchLocationsForReadableFiles getfp stopAtFirst locs suffs fp
  = fmap (map tup1234to124) $ searchLocationsForReadableFilesWith getfp stopAtFirst locs (map (flip (,) ()) suffs) fp
{-
  = let select stop f fps
          = foldM chk [] fps
          where chk r fp
                  = case r of
                      (_:_) | stop -> return r
                      _            -> do r' <- f fp
                                         return (r ++ r')
        tryToOpen loc mbSuff fp
          = do { let fp' = maybe fp (\suff -> fpathSetNonEmptySuff suff fp) mbSuff
               ; fExists <- doesFileExist (fpathToStr fp')
               -- ; hPutStrLn stderr (show fp ++ " - " ++ show fp')
               ; if fExists
                 then return [(fp',loc)]
                 else return []
               }
        tryToOpenWithSuffs suffs (loc,fp,x)
          = fmap (map (tup12to123 x)) $
            case suffs of
              [] -> tryToOpen loc Nothing fp
              _  -> select stopAtFirst
                      (\(ms,f) -> tryToOpen loc ms f)
                      ({- (Nothing,fp) : -} zipWith (\s f -> (s,f)) suffs (repeat fp))
        tryToOpenInDir loc
          = select True (tryToOpenWithSuffs suffs) (getfp loc fp)
     in select True tryToOpenInDir locs
-}

searchPathForReadableFiles :: Bool -> SearchPath -> FileSuffixes -> FPath -> IO [FPath]
searchPathForReadableFiles stopAtFirst locs suffs fp
  = fmap (map tup123to1) $ searchLocationsForReadableFiles (\s f -> map (tup12to123 ([]::[String])) $ searchFPathFromLoc s f) stopAtFirst locs suffs fp

searchPathForReadableFile :: SearchPath -> FileSuffixes -> FPath -> IO (Maybe FPath)
searchPathForReadableFile paths suffs fp
  = do fs <- searchPathForReadableFiles True paths suffs fp
       return (listToMaybe fs)

-------------------------------------------------------------------------------------------
-- Get modification time, with old-time + time compatibility
-------------------------------------------------------------------------------------------

fpathGetModificationTime :: FPath -> IO UTCTime
fpathGetModificationTime fp = getModificationTime (fpathToStr fp)
