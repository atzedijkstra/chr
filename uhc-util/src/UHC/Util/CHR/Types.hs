{-# LANGUAGE ScopedTypeVariables #-}

-------------------------------------------------------------------------------------------
--- Some shared types
-------------------------------------------------------------------------------------------

module UHC.Util.CHR.Types
  ( IVar
  
  , VarToNmMp
  , emptyVarToNmMp
  
  , NmToVarMp
  , emptyNmToVarMp
  )
  where

import qualified Data.Map                   as Map
import qualified Data.IntMap                as IntMap

-------------------------------------------------------------------------------------------
--- Name <-> Var mapping
-------------------------------------------------------------------------------------------

type IVar      = IntMap.Key

type VarToNmMp = IntMap.IntMap   String
type NmToVarMp = Map.Map         String  IVar

emptyVarToNmMp :: VarToNmMp = IntMap.empty
emptyNmToVarMp :: NmToVarMp = Map.empty
