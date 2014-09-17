{-# LANGUAGE CPP #-}

-- | Pretty-print the AuxAST to valid Epic code.
module Agda.Compiler.UHC.Core
  ( toCore
  , coreError
  ) where

import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Maybe (fromJust)

import Agda.TypeChecking.Monad
import Agda.Syntax.Abstract.Name
import Control.Monad.IO.Class
import Control.Monad.Trans.Class (lift)

import Agda.Compiler.UHC.AuxAST
import Agda.Compiler.UHC.CompileState
import Agda.Compiler.UHC.Interface

import EH99.Opts
import EH99.Core
import EH99.AbstractCore
import EH99.Base.HsName
import EH99.Base.Common
import EH99.Core.Parser
import UHC.Util.ParseUtils
import UHC.Util.ScanUtils
import EH99.Scanner.Common

import Agda.Compiler.UHC.CoreSyntax

import Agda.Utils.Impossible


toCore :: String -> [Fun] -> Compile TCM CModule
toCore mod funs = do
  binds <- mapM funToBind funs
  let mainEhc = CExpr_Let CBindCateg_Plain [
	CBind_Bind (hsnFromString "main") [
		CBound_Bind cmetas (appS "UHC.Run.ehcRunMain" (CExpr_Var $ acoreMkRef $ toCoreName $ ANmAgda (mod ++ ".main")))]
	] (CExpr_Var (acoreMkRef $ hsnFromString "main"))
  let lets = CExpr_Let CBindCateg_Rec binds mainEhc

  constrs <- getsEI constrTags
  cMetaDeclL <- buildCMetaDeclL constrs

  return $ CModule_Mod (hsnFromString $ "AgdaPU." ++ mod) [CImport_Import $ hsnFromString "UHC.Agda.Builtins"] cMetaDeclL lets

buildCMetaDeclL :: M.Map QName Tag -> Compile TCM CDeclMetaL
buildCMetaDeclL m = do
    dataCons <- mapM f (M.toList m)
    let dataCons' = M.toList $ M.unionsWith (++) dataCons
    
    return $ map (\(tyNm, dConL) -> CDeclMeta_Data tyNm dConL) dataCons'
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
  return $ CBind_Bind (toCoreName name) aspects
  where mkLambdas :: AName -> CExpr -> CExpr
        mkLambdas v body = CExpr_Lam (CBind_Bind (toCoreName v) []) body
funToBind (CoreFun name _ _ crExpr) = return $ CBind_Bind (toCoreName name) [CBound_Bind cmetas crExpr]

cmetas = (CMetaBind_Plain, CMetaVal_Val)

exprToCore :: MonadTCM m => Expr -> Compile m CExpr
exprToCore (Var v)      = return $ CExpr_Var (acoreMkRef $ toCoreName v)
exprToCore (Lit l)      = return $ litToCore l
exprToCore (Lam v body) = exprToCore body >>= return . CExpr_Lam (CBind_Bind (toCoreName v) [])
exprToCore (Con t qn es) = do
    es' <- mapM exprToCore es
    let ctor = CExpr_Tup $ mkCTag t qn
    return $ foldl (\x e -> app x e) ctor es'
exprToCore (App fv es)   = do
    es' <- mapM exprToCore es
    let fv' = CExpr_Var (acoreMkRef $ toCoreName fv)
    return $ foldl (\x e -> app x e) fv' es'
exprToCore (Case e brs) = do
    var <- newName
    (def, branches) <- branchesToCore brs
    let cas = CExpr_Case (CExpr_Var (acoreMkRef $ toCoreName var)) branches def
    e' <- exprToCore e
    return $ CExpr_Let CBindCateg_Strict [CBind_Bind (toCoreName var) [CBound_Bind cmetas e']] cas
exprToCore (Let v e1 e2) = do
    e1' <- exprToCore e1
    e2' <- exprToCore e2
-- TODO do we really need let-rec here?
    return $ CExpr_Let CBindCateg_Rec [CBind_Bind (toCoreName v)
                                [CBound_Bind cmetas e1']] e2'
exprToCore UNIT         = return $ coreUnit
exprToCore IMPOSSIBLE   = return $ coreImpossible

branchesToCore :: MonadTCM m => [Branch] -> Compile m (CExpr, CAltL)
branchesToCore brs = do
    let defs = filter isDefault brs
    def <- if null defs then return coreImpossible else let (Default x) = head defs in exprToCore x
    brs' <- mapM f brs

    return (def, concat brs')
    where
          f (Branch tag qn vars e)  = do
            -- TODO fix up everything
            let ctag = mkCTag tag qn
            let binds = [CPatFld_Fld (hsnFromString "") (CExpr_Int i) (CBind_Bind (toCoreName v) []) [] | (i, v) <- zip [0..] vars]
            e' <- exprToCore e
            return [CAlt_Alt (CPat_Con ctag CPatRest_Empty binds) e']
          f (CoreBranch con vars e) = do
            let ctag = conSpecToTag con
            let binds = [CPatFld_Fld (hsnFromString "") (CExpr_Int i) (CBind_Bind (toCoreName v) []) [] | (i, v) <- zip [0..] vars]
            e' <- exprToCore e
            return [CAlt_Alt (CPat_Con ctag CPatRest_Empty binds) e']
          f (BrInt _ _) = error "TODO"
          f (Default e) = return []
          -- UHC resets the tags for some constructors, but only those wo are defined in the same module. So just set it anyway, to be safe.
          conSpecToTag (dt, ctor, tag) = CTag (hsnFromString dt) (hsnFromString $ (modNm dt) ++ "." ++ ctor) (fromIntegral tag) 0 0
          modNm s = reverse $ tail $ dropWhile (/= '.') $ reverse s
          isDefault (Default _) = True
          isDefault _ = False

qnameTypeName :: QName -> HsName
qnameTypeName = toCoreName . unqname . qnameFromList . init . qnameToList

qnameCtorName :: QName -> HsName
qnameCtorName = hsnFromString . show . last . qnameToList

mkCTag :: Tag -> QName -> CTag
mkCTag (Tag t) qn = CTag (qnameTypeName qn) (qnameCtorName qn) t 0 0

litToCore :: Lit -> CExpr
-- should we put this into a let?
litToCore (LInt i) = appS "UHC.Agda.Builtins.primIntegerToNat" (appS "UHC.Base.primIntToInteger" (CExpr_Int $ fromInteger i))
litToCore (LString s) = coreStr s
litToCore l = error $ "Not implemented literal: " ++ show l

coreImpossible :: CExpr
coreImpossible = coreError "BUG! Impossible code reached."

coreError :: String -> CExpr
--should we put the string into a let?
coreError msg = appS "UHC.Base.error" (coreStr $ "AGDA: " ++ msg)
--coreError msg = "(UHC.Base.error) ((UHC.Base.packedStringToString) (#String\"" ++ msg ++ "\"))"

coreStr :: String -> CExpr
coreStr s = appS "UHC.Base.packedStringToString" (CExpr_String s)

coreUnit :: CExpr
coreUnit = CExpr_Tup CTagRec

toCoreName :: AName -> HsName
toCoreName (ANmCore n) = hsnFromString n
toCoreName (ANmAgda n) = hsnFromString $
    case elemIndex '.' nr of
        Just i -> let (n', ns') = splitAt i nr
                   in "AgdaPU." ++ (reverse ns') ++ "agda_c1_" ++ (reverse n')
        Nothing -> n -- local (generated) name
    where nr = reverse n

-- | Apply a lambda to one argument.
app :: CExpr -> CExpr -> CExpr
app f x = CExpr_App f (CBound_Bind cmetas x)

-- | Apply the named function to one argument.
appS :: String -> CExpr -> CExpr
appS f = app (CExpr_Var $ acoreMkRef $ hsnFromString f)
