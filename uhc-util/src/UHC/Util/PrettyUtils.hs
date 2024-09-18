module UHC.Util.PrettyUtils where

import UHC.Util.Pretty

-------------------------------------------------------------------------
-- Utils for tools: making LaTeX
-------------------------------------------------------------------------

mkTexCmdDef :: (PP cmd, PP a, PP b) => cmd -> a -> b -> PP_Doc
mkTexCmdDef cmd nm def = "\\" >|< pp cmd >|< "{" >|< pp nm >|< "}{%" >-< pp def >-< "}"

mkTexCmdUse :: (PP cmd, PP a) => cmd -> a -> PP_Doc
mkTexCmdUse cmd nm = "\\" >|< pp cmd >|< "{" >|< pp nm >|< "}"

mkTexCmdUse' :: (PP cmd, PP a) => cmd -> a -> PP_Doc
mkTexCmdUse' cmd nm = mkTexCmdUse cmd nm >|< "%"


