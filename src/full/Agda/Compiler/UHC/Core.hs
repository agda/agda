{-# LANGUAGE CPP #-}

-- | Pretty-print the AuxAST to valid Epic code.
module Agda.Compiler.UHC.Core
--  ( prettyEpicFun
--  , prettyEpic
--  ) where
  ( toCore
  , coreError
  ) where

import Data.Char
import Data.List
import qualified Data.Map as M

import Agda.TypeChecking.Monad
import Agda.Syntax.Abstract.Name
import Control.Monad.Trans.Class (lift)

import Agda.Compiler.UHC.AuxAST
import Agda.Compiler.UHC.CompileState
import Agda.Compiler.UHC.Interface

import EH99.Core
import EH99.AbstractCore
import EH99.Base.HsName
import EH99.Base.Common

-- #include "../../undefined.h"
--import Agda.Utils.Impossible



toCore :: String -> [Fun] -> Compile TCM CModule
toCore mod funs = do
  binds <- mapM funToBind funs
  let lets = CExpr_Let CBindCateg_Rec binds (CExpr_Int 0)

  constrs <- getsEI constrTags
  cMetaDeclL <- buildCMetaDeclL constrs

  return $ CModule_Mod (hsnFromString mod) cMetaDeclL lets

buildCMetaDeclL :: M.Map QName Tag -> Compile TCM CDeclMetaL
buildCMetaDeclL m = do
    dataCons <- mapM f (M.toList m)
    let dataCons' = M.unionsWith (++) dataCons
    
    return $ map (\(tyNm, dConL) -> CDeclMeta_Data tyNm dConL) (M.toList dataCons')
    where f :: (QName, Tag) -> Compile TCM (M.Map HsName [CDataCon])
          f (qn, (Tag t)) = do
              cr <- (lift $ getConstInfo qn) >>= return . compiledCore . defCompiledRep
              case cr of
                (Just _) -> return M.empty
                _ -> do
                  a <- getConArity qn
                  -- TODO do we have to put full qn into con name?
                  return $ M.singleton (qnameTypeName qn) [CDataCon_Con (hsnFromString $ show qn) t a]

funToBind :: MonadTCM m => Fun -> Compile m CBind
-- TODO Just put everything into one big let rec. Is this actually valid Core?
-- Maybe bad for optimizations?
funToBind (Fun _ name mqname comment vars e) = do -- TODO what is mqname?
  e' <- exprToCore e
  let aspects = [CBound_Bind cmetas (foldr mkLambdas e' vars)]
  return $ CBind_Bind (hsnFromString name) aspects
  where mkLambdas :: Var -> CExpr -> CExpr
        mkLambdas v body = CExpr_Lam (CBind_Bind (hsnFromString v) []) body
funToBind (CoreFun name _ _ crExpr) = return $ CBind_Bind (hsnFromString name) [CBound_Bind cmetas crExpr]

cmetas = (CMetaBind_Plain, CMetaVal_Val)

exprToCore :: MonadTCM m => Expr -> Compile m CExpr
exprToCore (Var v)      = return $ CExpr_Var (acoreMkRef $ hsnFromString v)
exprToCore (Lit l)      = return $ litToCore l
exprToCore (Lam v body) = exprToCore body >>= return . CExpr_Lam (CBind_Bind (hsnFromString v) [])
exprToCore (Con t qn es) = do
    es' <- mapM exprToCore es
    let ctor = CExpr_Tup $ mkCTag t qn
    return $ foldl (\x e -> CExpr_App x (CBound_Bind cmetas e)) ctor es'
exprToCore (App fv es)   = do
    es' <- mapM exprToCore es
    let fv' = CExpr_Var (acoreMkRef $ hsnFromString fv)
    return $ foldl (\x e -> CExpr_App x (CBound_Bind cmetas e)) fv' es'
exprToCore (Case e brs) = do
    var <- newName
    (def, branches) <- branchesToCore brs
    let cas = CExpr_Case (CExpr_Var (acoreMkRef $ hsnFromString var)) branches def
    e' <- exprToCore e
    return $ CExpr_Let CBindCateg_Strict [CBind_Bind (hsnFromString var) [CBound_Bind cmetas e']] cas
exprToCore (Let v e1 e2) = do
    e1' <- exprToCore e1
    e2' <- exprToCore e2
-- TODO do we really need let-rec here?
    return $ CExpr_Let CBindCateg_Rec [CBind_Bind (hsnFromString v)
                                [CBound_Bind cmetas e1']] e2'
exprToCore UNIT         = return $ coreUnit
exprToCore IMPOSSIBLE   = return $ coreImpossible

branchesToCore :: MonadTCM m => [Branch] -> Compile m (CExpr, CAltL)
branchesToCore brs = do
    let defs = filter isDefault brs
    def <- if null defs then return coreImpossible else let (Default x) = head defs in exprToCore x
    brs' <- mapM f brs

    return (def, concat brs')
    where f (Branch tag qn vars e)  = do
            -- TODO fix up everything
            let ctag = mkCTag tag qn
            let binds = [CPatFld_Fld (hsnFromString "") (CExpr_Int i) (CBind_Bind (hsnFromString v) []) [] | (i, v) <- zip [0..] vars]
            e' <- exprToCore e
            return [CAlt_Alt (CPat_Con ctag CPatRest_Empty binds) e']
          f (CoreBranch dt ctor tag vars e) = do
            let ctag = CTag (hsnFromString dt) (hsnFromString ctor) (fromIntegral tag) 0 0
            let binds = [CPatFld_Fld (hsnFromString "") (CExpr_Int i) (CBind_Bind (hsnFromString v) []) [] | (i, v) <- zip [0..] vars]
            e' <- exprToCore e
            return [CAlt_Alt (CPat_Con ctag CPatRest_Empty binds) e']
          f (BrInt _ _) = error "TODO"
          f (Default e) = return []
          isDefault (Default _) = True
          isDefault _ = False

qnameTypeName :: QName -> HsName
qnameTypeName = hsnFromString . unqname . qnameFromList . init . qnameToList

qnameCtorName :: QName -> HsName
qnameCtorName = hsnFromString . show . last . qnameToList

mkCTag :: Tag -> QName -> CTag
mkCTag (Tag t) qn = CTag (qnameTypeName qn) (qnameCtorName qn) t 0 0

litToCore :: Lit -> CExpr
-- should we put this into a let?
litToCore (LInt i) = CExpr_App (CExpr_Var $ acoreMkRef $ hsnFromString "UHC.Base.primIntToInteger") (CBound_Bind cmetas (CExpr_Int $ fromInteger i))
litToCore (LString s) = coreStr s
litToCore l = error $ "Not implemented literal: " ++ show l

coreImpossible :: CExpr
coreImpossible = coreError "BUG! Impossible code reached."

coreError :: String -> CExpr
--should we put the string into a let?
coreError msg = CExpr_App (CExpr_Var $ acoreMkRef $ hsnFromString "UHC.Base.error") (CBound_Bind cmetas (coreStr msg))
--coreError msg = "(UHC.Base.error) ((UHC.Base.packedStringToString) (#String\"" ++ msg ++ "\"))"

coreStr :: String -> CExpr
coreStr s = CExpr_App (CExpr_Var $ acoreMkRef $ hsnFromString "UHC.Base.packedStringToString") (CBound_Bind cmetas (CExpr_String s))

coreUnit :: CExpr
coreUnit = CExpr_Int 0

