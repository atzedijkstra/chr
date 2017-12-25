{-# LANGUAGE TypeSynonymInstances #-}

-------------------------------------------------------------------------
-- Subset of UU.Pretty, based on very simple pretty printing
-------------------------------------------------------------------------

module CHR.Pretty.Simple
  ( PP_Doc, PP(..)
  , disp
  , hPut
  , Doc(..)

  , (>|<), (>-<)
  , (>#<)
  , hlist, hlistReverse, vlist, hv
  , fill
  , indent

{-
  , pp_wrap, pp_quotes, pp_doubleQuotes, pp_parens, pp_brackets, pp_braces
  , ppPacked, ppParens, ppBrackets, ppBraces, ppCurlys
-}

  , empty, text
  
  -- * Internal use only
  , isSingleLine
  )
  where

import System.IO
-- import Data.Data
import Data.Typeable

-------------------------------------------------------------------------
-- Doc structure
-------------------------------------------------------------------------

-- | Cached info about combi of sub Docs
data Cached = Cached
    { cchEmp :: !Bool       -- ^ is it empty
    , cchSng :: !Bool       -- ^ is it a single line
    }
  deriving (Typeable)

-- | Doc structure
data Doc
  = Emp
  | Str         !String                 -- basic string
  | Hor         !Cached !Doc  !Doc      -- horizontal positioning
  | Ver         !Cached !Doc  !Doc      -- vertical positioning
  | Ind         !Int !Doc               -- indent
  deriving (Typeable)

type PP_Doc = Doc

-------------------------------------------------------------------------
-- Basic combinators
-------------------------------------------------------------------------

infixr 3 >|<, >#<
infixr 2 >-<

cached :: (PP a, PP b) => (PP_Doc -> PP_Doc -> Cached) -> (Cached -> PP_Doc -> PP_Doc -> PP_Doc) -> a -> b -> PP_Doc
cached cchd mk l r = mk (cchd l' r') l' r'
  where l' = pp l
        r' = pp r

-- | PP horizontally aside
(>|<) :: (PP a, PP b) => a -> b -> PP_Doc
l >|< r = cached mkcch Hor l r -- pp l `Hor` pp r
  where mkcch l r = Cached emp sng
          where emp = isEmpty l && isEmpty r
                sng = isSingleLine l && isSingleLine r

-- | PP vertically above
(>-<) :: (PP a, PP b) => a -> b -> PP_Doc
l >-< r = cached mkcch Ver l r -- pp l `Ver` pp r   -- pp l <$$> pp r
  where mkcch l r = Cached (empl && empr) sng
          where empl = isEmpty l
                empr = isEmpty r
                sng  = empl && isSingleLine r || empr && isSingleLine l

-- | PP horizontally aside with 1 blank in between
(>#<) :: (PP a, PP b) => a -> b -> PP_Doc
l >#< r  =  l >|< " " >|< r

-- | Indent
indent :: PP a => Int -> a -> PP_Doc
indent i d = Ind i $ pp d
{-# INLINE indent #-}

-- | basic string
text :: String -> PP_Doc
text = Str
{-# INLINE text #-}

-- | empty PP
empty :: PP_Doc
empty = Emp
{-# INLINE empty #-}

-------------------------------------------------------------------------
-- Derived combinators
-------------------------------------------------------------------------

vlist, hlist, hlistReverse :: PP a => [a] -> PP_Doc
-- | PP list horizontally
vlist [] = empty
vlist as = foldr  (>-<) empty as

-- | PP list vertically
hlist [] = empty
hlist as = foldr  (>|<) empty as

-- | PP list vertically reverse
hlistReverse [] = empty
hlistReverse as = foldr (flip (>|<)) empty as

-- | PP list vertically, alias for 'vlist'
hv :: PP a => [a] -> PP_Doc
hv = vlist

-- | PP list horizontally, alias for 'hlist'
fill :: PP a => [a] -> PP_Doc
fill = hlist

-------------------------------------------------------------------------
-- PP class
-------------------------------------------------------------------------

-- | Interface for PP
class Show a => PP a where
  pp     :: a   -> PP_Doc
  pp       = text . show

  ppList :: [a] -> PP_Doc
  ppList as = hlist as

instance PP PP_Doc where
  pp     = id

instance PP Char where
  pp c   = text [c]
  ppList = text

instance PP a => PP [a] where
  pp = ppList

instance Show PP_Doc where
  show p = disp p 200 ""

instance PP Int where
  pp = text . show

instance PP Integer where
  pp = text . show

instance PP Float where
  pp = text . show

-------------------------------------------------------------------------
-- Observation
-------------------------------------------------------------------------

-- | Is empty doc?
isEmpty :: PP_Doc -> Bool
isEmpty Emp           = True
isEmpty (Ver c d1 d2) = cchEmp c
isEmpty (Hor c d1 d2) = cchEmp c
isEmpty (Ind _  d   ) = isEmpty d
isEmpty (Str _      ) = False

-- | Is single line doc?
isSingleLine :: PP_Doc -> Bool
isSingleLine Emp           = True
isSingleLine (Ver c d1 d2) = cchSng c
isSingleLine (Hor c d1 d2) = cchSng c
isSingleLine (Ind _  d   ) = isSingleLine d
isSingleLine (Str _      ) = True

-------------------------------------------------------------------------
-- Rendering
-------------------------------------------------------------------------

-- | Display to string
disp  ::  PP_Doc -> Int -> ShowS
disp d _ s
  = r
  where (r,_) = put 0 d s
        put p d s
          = case d of
              Emp              -> (s,p)
              Str s'           -> (s' ++ s,p + length s')
              Ind i  d         -> (ind ++ r,p')
                               where (r,p') = put (p+i) d s
                                     ind = replicate i ' '
              Hor _ d1 d2      -> (r1,p2)
                               where (r1,p1) = put p  d1 r2
                                     (r2,p2) = put p1 d2 s
              Ver _ d1 d2 | isEmpty d1
                               -> put p d2 s
              Ver _ d1 d2 | isEmpty d2
                               -> put p d1 s
              Ver _ d1 d2        -> (r1,p2)
                               where (r1,p1) = put p d1 $ "\n" ++ ind ++ r2
                                     (r2,p2) = put p d2 s
                                     ind = replicate p ' '

-- | Display to Handle
hPut  :: Handle -> PP_Doc -> Int -> IO ()
hPut h d _
  = do _ <- put 0 d h
       return ()
  where put p d h
          = case d of
              Emp              -> return p
              Str s            -> do hPutStr h s
                                     return $ p + length s
              Ind i  d         -> do hPutStr h $ replicate i ' '
                                     put (p+i) d h
              Hor _ d1 d2      -> do p' <- put p d1 h
                                     put p' d2 h
              Ver _ d1 d2 | isEmpty d1
                               -> put p d2 h
              Ver _ d1 d2 | isEmpty d2
                               -> put p d1 h
              Ver _ d1 d2      -> do _ <- put p d1 h
                                     hPutStr h $ "\n" ++ replicate p ' '
                                     put p d2 h
