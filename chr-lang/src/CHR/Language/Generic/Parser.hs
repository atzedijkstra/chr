{-# LANGUAGE RankNTypes #-}

module CHR.Language.Generic.Parser
  ( parseFile
  )
  where

import qualified Data.Set as Set

import           Control.Monad
import           Control.Monad.State

import           CHR.Parse
import           CHR.Scan
import           CHR.Pretty

import           CHR.Types
import           CHR.Types.Rule
import           CHR.Language.Generic.AST

-------------------------------------------------------------------------------------------
--- Scanning options for CHR parsing
-------------------------------------------------------------------------------------------

-- | Scanning options for rule parser
scanOpts :: ScanOpts
scanOpts
  =  defaultScanOpts
        {   scoKeywordsTxt      =   Set.fromList []
        ,   scoKeywordsOps      =   Set.fromList ["\\", "=>", "==>", "<=>", ".", ":", "::", "@", "|", "\\/", "?"]
        ,   scoOpChars          =   Set.fromList "!#$%&*+/<=>?@\\^|-:.~"
        ,   scoSpecChars        =   Set.fromList "()[],`"
        }

-------------------------------------------------------------------------------------------
--- Parse interface
-------------------------------------------------------------------------------------------

-- | Parse a file as a CHR spec + queries
parseFile :: GTermAs c g bp rp => FilePath -> IO (Either PP_Doc ([Rule c g bp rp], [c], NmToVarMp))
parseFile f = do
    toks <- scanFile
      (Set.toList $ scoKeywordsTxt scanOpts)
      (Set.toList $ scoKeywordsOps scanOpts)
      (Set.toList $ scoSpecChars scanOpts)
      (Set.toList $ scoOpChars scanOpts)
      f
    (prog, query) <- parseIOMessage show pProg toks
    return $ fmap (\((r,c),s) -> (r, c, _gtermasNmToVarMp s)) $ flip runStateT emptyGTermAsState $ do
      prog <- forM prog $ \r@(Rule {ruleHead=hcs, ruleGuard=gs, ruleBodyAlts=as, ruleBacktrackPrio=mbp, rulePrio=mrp}) -> do
        mbp <- maybe (return Nothing) (fmap Just . asHeadBacktrackPrio) mbp
        mrp <- maybe (return Nothing) (fmap Just . asRulePrio) mrp
        hcs <- forM hcs asHeadConstraint
        gs  <- forM gs  asGuard
        as  <- forM as $ \a@(RuleBodyAlt {rbodyaltBacktrackPrio=mbp, rbodyaltBody=bs}) -> do
          mbp <- maybe (return Nothing) (fmap Just . asAltBacktrackPrio) mbp
          bs  <- forM bs asBodyConstraint
          return $ a {rbodyaltBacktrackPrio=mbp, rbodyaltBody=bs}
        return $ r {ruleHead=hcs, ruleGuard=gs, ruleBodyAlts=as, ruleBacktrackPrio=mbp, rulePrio=mrp}
      query <- forM query asHeadConstraint
      return (prog,query)

-------------------------------------------------------------------------------------------
--- Program is set of rules + optional queries
-------------------------------------------------------------------------------------------

type Pr p = PlainParser Token p

-- | CHR Program = rules + optional queries
pProg :: Pr ([Rule GTm GTm GTm GTm], [GTm])
pProg =
    pRules <+> pQuery
  where
    pR = pPre <**>
           ( pHead <**>
               (   (   (\(g,b) h pre -> pre $ g $ mkR h (length h) b) <$ pKey "<=>"
                   <|> (\(g,b) h pre -> pre $ g $ mkR h 0          b) <$ (pKey "=>" <|> pKey "==>")
                   ) <*> pBody
               <|> (   (\hr (g,b) hk pre -> pre $ g $ mkR (hr ++ hk) (length hr) b)
                       <$ pKey "\\" <*> pHead <* pKey "<=>" <*> pBody
                   )
               )
           )
       where pPre = (\(bp,rp) lbl -> lbl . bp . rp) 
                    <$> (pParens ((,) <$> (flip (=!) <$> pTm_Var <|> pSucceed id)
                                      <*  pComma
                                      <*> (flip (=!!) <$> pTm <|> pSucceed id)
                                 ) <* pKey "::" <|> pSucceed (id,id)
                        )
                    <*> ((@=) <$> (pConid <|> pVarid) <* pKey "@" <|> pSucceed id)
             pHead = pList1Sep pComma pTm_App
             pGrd = flip (=|) <$> pList1Sep pComma pTm_Op <* pKey "|" <|> pSucceed id
             pBody = pGrd <+> pBodyAlts
             pBodyAlts = pListSep (pKey "\\/") pBodyAlt
             pBodyAlt
               = (\pre b -> pre $ b /\ [])
                 <$> (flip (\!) <$> pTm <* pKey "::" <|> pSucceed id)
                 <*> pList1Sep pComma pTm_Op
             mkR h len b = Rule h len [] b Nothing Nothing Nothing

    pRules = pList (pR <* pKey ".")

    pQuery = concat <$> pList (pKey "?" *> pList1Sep pComma pTm_Op <* pKey ".")
    
    pTm
      = pTm_Op

    pTm_Op
      = pTm_App <**>
          (   (\o r l -> GTm_Con o [l,r]) <$> pOp <*> pTm_App
          <|> pSucceed id
          )
      where pOp
              =   pConsym
              <|> pVarsym
              <|> pKey "`" *> pConid <* pKey "`"
              <|> pCOLON

    pTm_App
      =   GTm_Con <$> pConid <*> pList1 pTm_Base
      <|> (\o l r -> GTm_Con o [l,r]) <$> pParens pVarsym <*> pTm_Base <*> pTm_Base
      <|> pTm_Base

    pTm_Base
      =   pTm_Var
      <|> (GTm_Int . read) <$> pInteger
      <|> GTm_Str <$> pString
      <|> flip GTm_Con [] <$> pConid
      <|> pParens pTm
      <|> pPacked (pKey "[") (pKey "]")
            (   pTm_App <**>
                  (   (\t h -> foldr1 GTm_Cns         (h:t)) <$ pCOLON   <*> pList1Sep  pCOLON    pTm_App
                  <|> (\t h -> foldr  GTm_Cns GTm_Nil (h:t)) <$ pKey "," <*> pList1Sep (pKey ",") pTm_App
                  <|> pSucceed (`GTm_Cns` GTm_Nil)
                  )
            <|> pSucceed GTm_Nil
            )

    pTm_Var
      = GTm_Var <$> pVarid

    pCOLON = pKey ":"


