{-# LANGUAGE CPP #-}

-- | Convert the AuxAST code to UHC Core code.
module Agda.Compiler.UHC.Core
  ( toCore
  , coreImpossible
  , mkHsName
  , createMainModule
  , getExportedExprs
  ) where

import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Maybe (fromJust, catMaybes)
import Control.Applicative
import qualified Data.Set as S

import Agda.TypeChecking.Monad
import Agda.Syntax.Abstract.Name
import Control.Monad.IO.Class
import Control.Monad.Trans.Class (lift)
import Control.Monad.State.Class
import Control.Monad.State

import Agda.Compiler.UHC.AuxAST hiding (apps)
import Agda.Compiler.UHC.Naming
import Agda.Compiler.UHC.ModuleInfo

import EH99.Core.API
import EH99.Base.HsName
import EH99.Base.Common
import EH99.Module.ImportExport

import Agda.Compiler.UHC.CoreSyntax

import Agda.Utils.Impossible

opts :: EHCOpts
opts = defaultEHCOpts


createMainModule :: String -> HsName -> CModule
createMainModule mainMod main = makeModule (mkHsName [] "Main") [makeImport $ mkHsName1 x | x <-
        [ "UHC.Run"
        , mainMod ]] [] (makeMain main)

getExportedExprs :: AModuleInfo -> ModEntRel
getExportedExprs mod = S.unions $ map f (M.elems $ getNameMappingFor nmMp EtFunction)
  where f nm | (cnAgdaExported nm || cnCoreExported nm) = mkEntRel (cnName nm)
        f _ = S.empty
        nmMp = amiCurNameMp mod
        mkEntRel :: HsName -> ModEntRel
        mkEntRel nm = S.singleton (snd $ hsnInitLast nm, ModEnt IdOcc_Val (IdOcc nm IdOcc_Val) S.empty Range_Unknown)


toCore :: AMod
    -> [AModuleInfo] -- ^ Top level imports
    -> TCM (CModule, S.Set HsName)
toCore mod modImps = do

  -- first, collect all qnames from the module. Then run the name assigner

  funs <- evalFreshNameT "nl.uu.agda.to_core" $ funsToCore (xmodFunDefs mod)

  let cMetaDeclL = buildCMetaDeclL (xmodDataTys mod)
  -- import resolution fails if we just use hsnFromString, as it produces a _Base hsname, but the Map used for the lookups stores _Modf names. Is this a bug?
  let imps = [ mkHsName1 x | x <-
        [ "UHC.Base"
        , "UHC.Agda.Builtins"
        ] ++ map (show . amiModule ) modImps]
  let impsCr = map makeImport imps
  let cmod = makeModule (hsnFromString $ show $ xmodName mod) impsCr cMetaDeclL funs
  let hiImps = S.fromList imps
  return (cmod, hiImps)

funsToCore :: Monad m => [Fun] -> FreshNameT m CExpr
funsToCore funs = do
  binds <- mapM funToBind funs
  let body = acoreLetRec binds (acoreInt opts 0)
  return body

buildCMetaDeclL :: [ADataTy] -> [CDeclMeta]
buildCMetaDeclL dts = map f dts
    where f :: ADataTy -> CDeclMeta
          f d@(ADataTy{}) = makeMetaData (xdatName d) (map g (xdatCons d))
          g :: ADataCon -> CDataCon
          g c@(ADataCon{}) = makeMetaDataCon (xconFullName c) (xconTag c) (xconArity c)


funToBind :: Monad m => Fun -> FreshNameT m CBind
funToBind (Fun _ name mqname comment vars e) = do -- TODO what is mqname?
  e' <- exprToCore e
  let body = acoreLam vars e'
  return $ acoreBind1 name body
funToBind (CoreFun name _ _ crExpr) = return $ acoreBind1 name crExpr

exprToCore :: Monad m => Expr -> FreshNameT m CExpr
exprToCore (Var v)      = return $ acoreVar v
exprToCore (Lit l)      = return $ litToCore l
exprToCore (Lam v body) = exprToCore body >>= return . acoreLam [v]
exprToCore (Con ty con es) = do
    es' <- mapM exprToCore es
    let ctag = mkCTag ty con
    return $ acoreTagTup ctag es'
exprToCore (App fv es)   = do
    es' <- mapM exprToCore es
    let fv' = acoreVar fv
    return $ acoreApp fv' es'
exprToCore (Case e brs) = do
    var <- freshLocalName
    (def, branches) <- branchesToCore brs
    let cas = acoreCaseDflt (acoreVar var) branches (Just def)
    e' <- exprToCore e
    return $ acoreLet1Strict var e' cas
exprToCore (Let v e1 e2) = do
    e1' <- exprToCore e1
    e2' <- exprToCore e2
    return $ acoreLet1Plain v e1' e2'
exprToCore UNIT         = return $ acoreUnit opts
exprToCore IMPOSSIBLE   = return $ coreImpossible ""

branchesToCore :: Monad m => [Branch] -> FreshNameT m (CExpr, [CAlt])
branchesToCore brs = do
    let defs = filter isDefault brs
    def <- if null defs then return (coreImpossible "Default branch reached, but doesn't exit.") else let (Default x) = head defs in exprToCore x
    brs' <- mapM f brs

    return (def, concat brs')
    where
          f (Branch ty con _ vars e)  = do
            let ctag = mkCTag ty con
            let patFlds = [acorePatFldBind (hsnFromString "", acoreInt opts i) (acoreBind1Nm1 v) | (i, v) <- zip [0..] vars]
            e' <- exprToCore e
            return [acoreAlt (acorePatCon ctag acorePatRestEmpty patFlds) e']
          f (CoreBranch con vars e) = do
            let ctag = conSpecToTag con
            let patFlds = [acorePatFldBind (hsnFromString "", acoreInt opts i) (acoreBind1Nm1 v) | (i, v) <- zip [0..] vars]
            e' <- exprToCore e
            return [acoreAlt (acorePatCon ctag acorePatRestEmpty patFlds) e']
          f (Default e) = return []
          -- UHC resets the tags for some constructors, but only those wo are defined in the same module. So just set it anyway, to be safe.
          conSpecToTag (dt, ctor, tag) = CTag (mkHsName1 dt) (mkHsName1 $ (modNm dt) ++ "." ++ ctor) tag (-1) (-1)
          modNm s = reverse $ tail $ dropWhile (/= '.') $ reverse s
          isDefault (Default _) = True
          isDefault _ = False

--qnameTypeName :: QName -> HsName
--qnameTypeName = toCoreName . unqname . qnameFromList . init . qnameToList

--qnameCtorName :: QName -> HsName
--qnameCtorName = mkHsName . show . last . qnameToList

mkCTag :: ADataTy -> ADataCon -> CTag
mkCTag ty con = CTag (xdatName ty) (xconFullName con) (xconTag con) (-1) (-1)

{-
mkCTag :: Tag
-> HsName -> CTag
mkCTag t nm = CTag (qnameTypeName qn) (qnameCtorName qn) t (-1) (-1)
-}

litToCore :: Lit -> CExpr
-- should we put this into a let?
litToCore (LInt i) = acoreApp (acoreVar $ mkHsName ["UHC", "Agda", "Builtins"] "primIntegerToNat") [acoreBuiltinInteger opts i]
litToCore (LString s) = acoreBuiltinString opts s
litToCore l = error $ "Not implemented literal: " ++ show l

coreImpossible :: String -> CExpr
coreImpossible msg = acoreBuiltinError opts $ "BUG! Impossible code reached. " ++ msg

