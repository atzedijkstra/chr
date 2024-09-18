{- |
A VarMp maps from variables (tvars, ...) to whatever else has to be
mapped to (Ty, ...).

Starting with variant 6 (which introduces kinds) it allows multiple meta
level mapping, in that the VarMp holds mappings for multiple meta
levels. This allows one map to both map to base level info and to higher
levels. In particular this is used by fitsIn which also instantiates
types, and types may quantify over type variables with other kinds than
kind *, which must be propagated. A separate map could have been used,
but this holds the info together and is extendible to more levels.

A multiple level VarMp knows its own absolute metalevel, which is the default to use for lookup.
-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
-- {-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE DeriveGeneric #-}

module UHC.Util.VarMp
    ( module CHR.Data.VarMp
    )
  where

import CHR.Data.VarMp
import UHC.Util.Serialize

instance (Ord k, Serialize k, Serialize v) => Serialize (VarMp' k v) where
  -- sput (VarMp a b) = sput a >> sput b
  -- sget = liftM2 VarMp sget sget

