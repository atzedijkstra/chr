{-# LANGUAGE RankNTypes, TypeSynonymInstances #-}

-------------------------------------------------------------------------
-- Wrapper module around pretty printing
-------------------------------------------------------------------------

module CHR.Pretty
  ( -- module UU.Pretty
    -- module UHC.Util.Chitil.Pretty
    module CHR.Pretty.Simple

  , PP_DocL

  -- * Choice combinators
  , (>-|-<)
  , (>-#-<)
  
  -- * General PP for list
  , ppListSep, ppListSepV, ppListSepVV
  
  -- * Pack PP around
  , ppCurlys
  , ppPacked
  , ppPackedWithStrings
  , ppParens
  , ppCurly
  , ppBrackets
  , ppVBar
  
  -- * Block, horizontal/vertical as required
  , ppBlock, ppBlockH
  , ppBlock'
  , ppBlockWithStrings
  , ppBlockWithStrings'
  , ppBlockWithStringsH
  
  , ppParensCommasBlock
  , ppCurlysBlock
  , ppCurlysSemisBlock
  , ppCurlysCommasBlock
  , ppParensSemisBlock
  , ppBracketsCommasBlock
  
  , ppParensCommasBlockH
  , ppCurlysBlockH
  , ppCurlysSemisBlockH
  , ppCurlysCommasBlockH
  , ppParensSemisBlockH
  , ppBracketsCommasBlockH
  
  , ppBracketsCommasV
  
  -- * Vertical PP of list only
  , ppVertically
  
  -- * Horizontal PP of list only
  , ppCommas, ppCommas'
  , ppSemis, ppSemis'
  , ppSpaces
  , ppCurlysCommas, ppCurlysCommas', ppCurlysCommasWith
  , ppCurlysSemis, ppCurlysSemis'
  , ppParensSpaces
  , ppParensCommas, ppParensCommas'
  , ppBracketsCommas
  , ppBracketsCommas'
  , ppHorizontally
  , ppListSepFill

  -- * Conditional
  , ppMbPre, ppMbPost
  , ppListPre, ppListPost

  -- * Misc
  , ppDots, ppMb, ppUnless, ppWhen

  -- * Render
  , showPP
  
  -- * IO
  , hPutWidthPPLn, putWidthPPLn
  , hPutPPLn, putPPLn
  , hPutPPFile, putPPFile
  -- , putPPFPath
  )
  where

-- import UU.Pretty
-- import UHC.Util.Chitil.Pretty
import           CHR.Pretty.Simple
-- import           CHR.Utils
-- import           UHC.Util.FPath
-- import           UHC.Util.Time
import           System.IO
import           Data.List
import           Data.Word
import qualified Data.Set as Set

-------------------------------------------------------------------------
-- PP utils for lists
-------------------------------------------------------------------------

type PP_DocL = [PP_Doc]

-- | PP list with open, separator, and close
ppListSep :: (PP s, PP c, PP o, PP a) => o -> c -> s -> [a] -> PP_Doc
ppListSep = ppListSepWith pp -- o >|< hlist (intersperse (pp s) (map pp pps)) >|< c
{-
ppListSep o c s pps
  = o >|< l pps >|< c
  where l []      = empty
        l [p]     = pp p
        l (p:ps)  = pp p >|< map (s >|<) ps
-}

-- | PP list with open, separator, and close, and explicit PP function
ppListSepWith :: (PP s, PP c, PP o) => (a->PP_Doc) -> o -> c -> s -> [a] -> PP_Doc
ppListSepWith ppa o c s pps = o >|< hlist (intersperse (pp s) (map ppa pps)) >|< c

{-# DEPRECATED ppListSepFill "Use ppListSep" #-}
ppListSepFill :: (PP s, PP c, PP o, PP a) => o -> c -> s -> [a] -> PP_Doc
ppListSepFill o c s pps
  = l pps
  where l []      = o >|< c
        l [p]     = o >|< pp p >|< c
        l (p:ps)  = hlist ((o >|< pp p) : map (s >|<) ps) >|< c

-- | PP in a blocklike fashion, possibly on a single horizontal line if indicated, yielding the lines of the block
ppBlock'' :: (PP ocs, PP a) => Bool -> ocs -> ocs -> ocs -> ocs -> [a] -> [PP_Doc]
ppBlock'' _    osngl _ c _ []                   = [osngl >|< c]
ppBlock'' _    osngl o c _ [a] | isSingleLine x = [osngl >|< x >|< c]
                               | otherwise      = [o >|< x] ++ [pp c]
                               where x = pp a
ppBlock'' hori osngl o c s aa@(a:as)               -- = [o >|< a] ++ map (s >|<) as ++ [pp c]
                               | hori && all isSingleLine xx = [osngl >|< x >|< hlist (map (s >|<) xs) >|< c]
                               | otherwise                   = [o >|< x] ++ map (s >|<) xs ++ [pp c]
                               where xx@(x:xs) = map pp aa

-- | PP in a blocklike fashion, vertically
ppBlock' :: (PP ocs, PP a) => ocs -> ocs -> ocs -> ocs -> [a] -> [PP_Doc]
ppBlock' = ppBlock'' False
{-# INLINE ppBlock' #-}

-- | PP in a blocklike fashion, vertically, possibly horizontally
ppBlockH' :: (PP ocs, PP a) => ocs -> ocs -> ocs -> ocs -> [a] -> [PP_Doc]
ppBlockH' = ppBlock'' True
{-# INLINE ppBlockH' #-}

-- | PP list with open, separator, and close in a possibly multiline block structure
ppBlock :: (PP ocs, PP a) => ocs -> ocs -> ocs -> [a] -> PP_Doc
ppBlock o c s = vlist . ppBlock' o o c s

-- | PP list with open, separator, and close in a possibly multiline block structure
ppBlockH :: (PP ocs, PP a) => ocs -> ocs -> ocs -> [a] -> PP_Doc
ppBlockH o c s = vlist . ppBlockH' o o c s

-- | See 'ppBlock', but with string delimiters aligned properly, yielding a list of elements
ppBlockWithStrings'' :: (PP a) => Bool -> String -> String -> String -> [a] -> [PP_Doc]
ppBlockWithStrings'' hori o c s = ppBlock'' hori o (pad o) c (pad s)
  where l = maximum $ map length [o,s]
        pad s = s ++ replicate (l - length s) ' '

-- | See 'ppBlock', but with string delimiters aligned properly, yielding a list of elements
ppBlockWithStrings' :: (PP a) => String -> String -> String -> [a] -> [PP_Doc]
ppBlockWithStrings' = ppBlockWithStrings'' False
{-# INLINE ppBlockWithStrings' #-}

-- | See 'ppBlock', but with string delimiters aligned properly, yielding a list of elements, preferring single line horizontal placement
ppBlockWithStringsH' :: (PP a) => String -> String -> String -> [a] -> [PP_Doc]
ppBlockWithStringsH' = ppBlockWithStrings'' True
{-# INLINE ppBlockWithStringsH' #-}

-- | See 'ppBlock', but with string delimiters aligned properly
ppBlockWithStrings :: (PP a) => String -> String -> String -> [a] -> PP_Doc
ppBlockWithStrings o c s = vlist . ppBlockWithStrings' o c s

-- | See 'ppBlock', but with string delimiters aligned properly, preferring single line horizontal placement
ppBlockWithStringsH :: (PP a) => String -> String -> String -> [a] -> PP_Doc
ppBlockWithStringsH o c s = vlist . ppBlockWithStringsH' o c s

-- | PP horizontally: list separated by comma
ppCommas :: PP a => [a] -> PP_Doc
ppCommas = ppListSep "" "" ","

-- | PP horizontally: list separated by comma + single blank
ppCommas' :: PP a => [a] -> PP_Doc
ppCommas' = ppListSep "" "" ", "

-- | PP horizontally: list separated by semicolon
ppSemis :: PP a => [a] -> PP_Doc
ppSemis = ppListSep "" "" ";"

-- | PP horizontally: list separated by semicolon + single blank
ppSemis' :: PP a => [a] -> PP_Doc
ppSemis' = ppListSep "" "" "; "

-- | PP horizontally: list separated by single blank
ppSpaces :: PP a => [a] -> PP_Doc
ppSpaces = ppListSep "" "" " "

-- | PP horizontally or vertically with "{", " ", and "}" in a possibly multiline block structure
ppCurlysBlock :: PP a => [a] -> PP_Doc
ppCurlysBlock = ppBlockWithStrings "{" "}" "  "
{-# INLINE ppCurlysBlock #-}

-- | PP horizontally or vertically with "{", " ", and "}" in a possibly multiline block structure, preferring single line horizontal placement
ppCurlysBlockH :: PP a => [a] -> PP_Doc
ppCurlysBlockH = ppBlockWithStringsH "{" "}" "  "
{-# INLINE ppCurlysBlockH #-}

-- | PP horizontally or vertically with "{", ";", and "}" in a possibly multiline block structure
ppCurlysSemisBlock :: PP a => [a] -> PP_Doc
ppCurlysSemisBlock = ppBlockWithStrings "{" "}" "; "
{-# INLINE ppCurlysSemisBlock #-}

-- | PP horizontally or vertically with "{", ";", and "}" in a possibly multiline block structure, preferring single line horizontal placement
ppCurlysSemisBlockH :: PP a => [a] -> PP_Doc
ppCurlysSemisBlockH = ppBlockWithStringsH "{" "}" "; "
{-# INLINE ppCurlysSemisBlockH #-}

-- | PP horizontally or vertically with "{", ",", and "}" in a possibly multiline block structure
ppCurlysCommasBlock :: PP a => [a] -> PP_Doc
ppCurlysCommasBlock = ppBlockWithStrings "{" "}" ", "
{-# INLINE ppCurlysCommasBlock #-}

-- | PP horizontally or vertically with "{", ",", and "}" in a possibly multiline block structure, preferring single line horizontal placement
ppCurlysCommasBlockH :: PP a => [a] -> PP_Doc
ppCurlysCommasBlockH = ppBlockWithStringsH "{" "}" ", "
{-# INLINE ppCurlysCommasBlockH #-}

-- | PP horizontally or vertically with "(", ";", and ")" in a possibly multiline block structure
ppParensSemisBlock :: PP a => [a] -> PP_Doc
ppParensSemisBlock = ppBlockWithStrings "(" ")" "; "
{-# INLINE ppParensSemisBlock #-}

-- | PP horizontally or vertically with "(", ";", and ")" in a possibly multiline block structure, preferring single line horizontal placement
ppParensSemisBlockH :: PP a => [a] -> PP_Doc
ppParensSemisBlockH = ppBlockWithStringsH "(" ")" "; "
{-# INLINE ppParensSemisBlockH #-}

-- | PP horizontally or vertically with "(", ",", and ")" in a possibly multiline block structure
ppParensCommasBlock :: PP a => [a] -> PP_Doc
ppParensCommasBlock = ppBlockWithStrings "(" ")" ", "
{-# INLINE ppParensCommasBlock #-}

-- | PP horizontally or vertically with "(", ",", and ")" in a possibly multiline block structure, preferring single line horizontal placement
ppParensCommasBlockH :: PP a => [a] -> PP_Doc
ppParensCommasBlockH = ppBlockWithStringsH "(" ")" ", "
{-# INLINE ppParensCommasBlockH #-}

-- | PP horizontally or vertically with "[", ",", and "]" in a possibly multiline block structure
ppBracketsCommasV, ppBracketsCommasBlock, ppBracketsCommasBlockH :: PP a => [a] -> PP_Doc
ppBracketsCommasBlock = ppBlockWithStrings "[" "]" ", "
{-# INLINE ppBracketsCommasBlock #-}
ppBracketsCommasBlockH = ppBlockWithStringsH "[" "]" ", "
{-# INLINE ppBracketsCommasBlockH #-}
ppBracketsCommasV = ppBracketsCommasBlock
{-# DEPRECATED ppBracketsCommasV "Use ppBracketsCommasBlock" #-}

-- | PP horizontally with "[", ",", and "]"
ppBracketsCommas :: PP a => [a] -> PP_Doc
ppBracketsCommas = ppListSep "[" "]" ","

-- | PP horizontally with "[", ", ", and "]"
ppBracketsCommas' :: PP a => [a] -> PP_Doc
ppBracketsCommas' = ppListSep "[" "]" ", "

-- | PP horizontally with "(", " ", and ")"
ppParensSpaces :: PP a => [a] -> PP_Doc
ppParensSpaces = ppListSep "(" ")" " "

-- | PP horizontally with "(", ",", and ")"
ppParensCommas :: PP a => [a] -> PP_Doc
ppParensCommas = ppListSep "(" ")" ","

-- | PP horizontally with "(", ", ", and ")"
ppParensCommas' :: PP a => [a] -> PP_Doc
ppParensCommas' = ppListSep "(" ")" ", "

-- | PP horizontally with "{", ",", and "}"
ppCurlysCommas :: PP a => [a] -> PP_Doc
ppCurlysCommas = ppListSep "{" "}" ","

ppCurlysCommasWith :: PP a => (a->PP_Doc) -> [a] -> PP_Doc
ppCurlysCommasWith ppa = ppListSepWith ppa "{" "}" ","

-- | PP horizontally with "{", ", ", and "}"
ppCurlysCommas' :: PP a => [a] -> PP_Doc
ppCurlysCommas' = ppListSep "{" "}" ", "

-- | PP horizontally with "{", ";", and "}"
ppCurlysSemis :: PP a => [a] -> PP_Doc
ppCurlysSemis = ppListSep "{" "}" ";"

-- | PP horizontally with "{", "; ", and "}"
ppCurlysSemis' :: PP a => [a] -> PP_Doc
ppCurlysSemis' = ppListSep "{" "}" "; "

{-
ppCommaListV :: PP a => [a] -> PP_Doc
ppCommaListV = ppListSepVV "[" "]" "; "
-}

{-# DEPRECATED ppListSepV', ppListSepV, ppListSepVV "Use pp...Block variants" #-}
ppListSepV' :: (PP s, PP c, PP o, PP a) => (forall x y . (PP x, PP y) => x -> y -> PP_Doc) -> o -> c -> s -> [a] -> PP_Doc
ppListSepV' aside o c s pps
  = l pps
  where l []      = o `aside` c
        l [p]     = o `aside` p `aside` c
        l (p:ps)  = vlist ([o `aside` p] ++ map (s `aside`) (init ps) ++ [s `aside` last ps `aside` c])

-- compact vertical list
{-
ppListSepV3 :: (PP s, PP c, PP o, PP a) => o -> c -> s -> [a] -> PP_Doc
ppListSepV3 o c s pps
  = l pps
  where l []      = o >|< c
        l [p]     = o >|< p >|< c
        l (p:ps)  = vlist ([o >|< p] ++ map (s >|<) (init ps) ++ [s >|< last ps >|< c])
-}

ppListSepV :: (PP s, PP c, PP o, PP a) => o -> c -> s -> [a] -> PP_Doc
ppListSepV = ppListSepV' (>|<)

ppListSepVV :: (PP s, PP c, PP o, PP a) => o -> c -> s -> [a] -> PP_Doc
ppListSepVV = ppListSepV' (>-<)

-- | Alias for 'vlist'
ppVertically :: [PP_Doc] -> PP_Doc
ppVertically = vlist

-- | Alias for 'hlist'
ppHorizontally :: [PP_Doc] -> PP_Doc
ppHorizontally = hlist

-------------------------------------------------------------------------
-- Printing open/close pairs
-------------------------------------------------------------------------

ppPacked :: (PP o, PP c, PP p) => o -> c -> p -> PP_Doc
ppPacked o c pp
  = o >|< pp >|< c

ppPackedWithStrings :: (PP p) => String -> String -> p -> PP_Doc
ppPackedWithStrings o c x = ppBlockWithStrings o c "" [x]

ppParens, ppBrackets, ppCurly, ppCurlys, ppVBar :: PP p => p -> PP_Doc
ppParens   = ppPackedWithStrings "(" ")"
ppBrackets = ppPackedWithStrings "[" "]"
ppCurly    = ppPackedWithStrings "{" "}"
ppCurlys   = ppCurly
ppVBar     = ppPackedWithStrings "|" "|"

-------------------------------------------------------------------------
-- Additional choice combinators, use with care...
-------------------------------------------------------------------------

infixr 2 >-|-<, >-#-<

aside :: (PP a, PP b) => String -> a -> b -> PP_Doc
aside sep l r | isSingleLine l' && isSingleLine r' = l' >|< sep >|< r'
              | otherwise                          = l' >-< sep >|< r'
  where l' = pp l
        r' = pp r

-- | As (>|<), but doing (>-<) when does not fit on single line
(>-|-<) :: (PP a, PP b) => a -> b -> PP_Doc
(>-|-<) = aside ""

-- | As (>#<), but doing (>-<) when does not fit on single line
(>-#-<) :: (PP a, PP b) => a -> b -> PP_Doc
(>-#-<) = aside " "

-------------------------------------------------------------------------
-- Conditional
-------------------------------------------------------------------------

maybeNull :: r -> ([a] -> r) -> [a] -> r
maybeNull n f l = if null l then n else f l
{-# INLINE maybeNull  #-}

-- | Only prefix with a 'Maybe' and extra space when 'Just'
ppMbPre :: (PP x, PP r) => (a -> x) -> Maybe a -> r -> PP_Doc
ppMbPre  p = maybe pp (\v rest -> p v >#< rest)

-- | Only suffix with a 'Maybe' and extra space when 'Just'
ppMbPost :: (PP x, PP r) => (a -> x) -> Maybe a -> r -> PP_Doc
ppMbPost p = maybe pp (\v rest -> rest >#< p v)

-- | Only prefix with a list and extra space when non-empty
ppListPre :: (PP x, PP r) => ([a] -> x) -> [a] -> r -> PP_Doc
ppListPre p = maybeNull pp (\l rest -> p l >#< rest)

-- | Only suffix with a list and extra space when non-empty
ppListPost :: (PP x, PP r) => ([a] -> x) -> [a] -> r -> PP_Doc
ppListPost p = maybeNull pp (\l rest -> p l >#< rest)

-- | Guard around PP: if False pass through
ppUnless :: PP x => Bool -> x -> PP_Doc
ppUnless b x = if b then empty else pp x

-- | Guard around PP: if True pass through
ppWhen :: PP x => Bool -> x -> PP_Doc
ppWhen b x = if b then pp x else empty

-------------------------------------------------------------------------
-- Misc
-------------------------------------------------------------------------

ppDots :: PP a => [a] -> PP_Doc
ppDots = ppListSep "" "" "."

ppMb :: PP a => Maybe a -> PP_Doc
ppMb = maybe empty pp

-------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------

instance {-# OVERLAPPABLE #-} PP a => PP (Maybe a) where
  pp = maybe (pp "?") pp

instance {-# OVERLAPPABLE #-} PP a => PP (Set.Set a) where
  pp = ppCurlysCommasBlockH . Set.toList

instance PP Bool where
  pp = pp . show

instance PP Word32 where
  pp = pp . show

{-
instance PP ClockTime where
  pp = pp . show

instance PP FPath where
  pp = pp . fpathToStr
-}

instance PP () where
  pp _ = pp "()"

instance (PP a, PP b) => PP (a,b) where
  pp (a,b) = "(" >|< a >-|-< "," >|< b >-|-< ")"

instance (PP a, PP b, PP c) => PP (a,b,c) where
  pp (a,b,c) = "(" >|< a >-|-< "," >|< b >-|-< "," >|< c >-|-< ")"

{-
instance (PP a, PP b, PP c, PP d) => PP (a,b,c,d) where
  pp (a,b,c,d) = ppParensCommasBlock [a,b,c,d]

instance (PP a, PP b, PP c, PP d, PP e) => PP (a,b,c,d,e) where
  pp (a,b,c,d,e) = ppParensCommasBlock [a,b,c,d,e]

instance (PP a, PP b, PP c, PP d, PP e, PP f) => PP (a,b,c,d,e,f) where
  pp (a,b,c,d,e,f) = ppParensCommasBlock [a,b,c,d,e,f]

instance (PP a, PP b, PP c, PP d, PP e, PP f, PP g) => PP (a,b,c,d,e,f,g) where
  pp (a,b,c,d,e,f,g) = ppParensCommasBlock [a,b,c,d,e,f,g]

instance (PP a, PP b, PP c, PP d, PP e, PP f, PP g, PP h) => PP (a,b,c,d,e,f,g,h) where
  pp (a,b,c,d,e,f,g,h) = ppParensCommasBlock [a,b,c,d,e,f,g,h]

instance (PP a, PP b, PP c, PP d, PP e, PP f, PP g, PP h, PP i) => PP (a,b,c,d,e,f,g,h,i) where
  pp (a,b,c,d,e,f,g,h,i) = ppParensCommasBlock [a,b,c,d,e,f,g,h,i]

instance (PP a, PP b, PP c, PP d, PP e, PP f, PP g, PP h, PP i, PP j) => PP (a,b,c,d,e,f,g,h,i,j) where
  pp (a,b,c,d,e,f,g,h,i,j) = ppParensCommasBlock [a,b,c,d,e,f,g,h,i,j]
-}

-------------------------------------------------------------------------
-- Render
-------------------------------------------------------------------------

showPP :: PP a => a -> String
showPP x = disp (pp x) 1000 ""

-------------------------------------------------------------------------
-- PP printing to file
-------------------------------------------------------------------------

hPutLn :: Handle -> Int -> PP_Doc -> IO ()
{-
hPutLn h w pp
  = do hPut h pp w
       hPutStrLn h ""
-}
hPutLn h w pp
  = hPutStrLn h (disp pp w "")

hPutWidthPPLn :: Handle -> Int -> PP_Doc -> IO ()
hPutWidthPPLn h w pp = hPutLn h w pp

putWidthPPLn :: Int -> PP_Doc -> IO ()
putWidthPPLn = hPutWidthPPLn stdout

hPutPPLn :: Handle -> PP_Doc -> IO ()
hPutPPLn h = hPutWidthPPLn h 4000

putPPLn :: PP_Doc -> IO ()
putPPLn = hPutPPLn stdout

hPutPPFile :: Handle -> PP_Doc -> Int -> IO ()
hPutPPFile h pp wid
  = hPutLn h wid pp

{-
putPPFPath :: FPath -> PP_Doc -> Int -> IO ()
putPPFPath fp pp wid
  = do { fpathEnsureExists fp
       ; putPPFile (fpathToStr fp) pp wid
       }
-}

putPPFile :: String -> PP_Doc -> Int -> IO ()
putPPFile fn pp wid
  =  do  {  h <- openFile fn WriteMode
         ;  hPutPPFile h pp wid
         ;  hClose h
         }
