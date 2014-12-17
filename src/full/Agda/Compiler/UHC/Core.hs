{-# LANGUAGE CPP #-}

-- | Convert the AuxAST code to UHC Core code.
module Agda.Compiler.UHC.Core
  ( toCore
  , coreImpossible
  , mkHsName
  , createMainModule
--  , getExportedExprs
  ) where

import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Maybe (fromJust, catMaybes, fromMaybe)
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

import UHC.Light.Compiler.Core.API

--import Agda.Compiler.UHC.Pragmas.Base

#include "undefined.h"
import Agda.Utils.Impossible

opts :: EHCOpts
opts = defaultEHCOpts


createMainModule :: String -> HsName -> CModule
createMainModule mainMod main = mkModule (mkHsName [] "Main") [] [mkImport $ mkHsName1 x | x <-
        [ "UHC.Run"
        , mainMod ]] [] (mkMain main)

getExports :: AModuleInfo -> [CExport]
getExports modInfo = map (mkExport . cnName) (expFuns ++ expConFuns)
  where funs = M.elems $ getNameMappingFor (amiCurNameMp modInfo) EtFunction
        expFuns = filter needsExport funs
        -- there is a function for each datatype, named as the datatype itself.
        -- This is used as type-dummy, returning always unit.
        -- We need to export those too.
        cons = M.elems $ getNameMappingFor (amiCurNameMp modInfo) EtDatatype
        expConFuns = filter needsExport cons
        needsExport x = cnAgdaExported x || cnCoreExported x

{-getExportedExprs :: AModuleInfo -> ModEntRel
getExportedExprs mod = S.unions $ map f (M.elems $ getNameMappingFor nmMp EtFunction)
  where f nm | (cnAgdaExported nm || cnCoreExported nm) = mkEntRel (cnName nm)
        f _ = S.empty
        nmMp = amiCurNameMp mod
        mkEntRel :: HsName -> ModEntRel
        mkEntRel nm = S.singleton (snd $ hsnInitLast nm, ModEnt IdOcc_Val (IdOcc nm IdOcc_Val) S.empty Range_Unknown)
-}

toCore :: AMod      -- ^ The current module to compile.
    -> AModuleInfo  -- ^ Info about current module.
    -> [AModuleInfo] -- ^ Top level imports
    -> TCM CModule
toCore mod modInfo modImps = do

  -- first, collect all qnames from the module. Then run the name assigner

  funs <- evalFreshNameT "nl.uu.agda.to_core" $ funsToCore (xmodFunDefs mod)

  let cMetaDeclL = buildCMetaDeclL (xmodDataTys mod)
  -- import resolution fails if we just use hsnFromString, as it produces a _Base hsname, but the Map used for the lookups stores _Modf names. Is this a bug?
  let imps = [ mkHsName1 x | x <-
        [ "UHC.Base"
        , "UHC.Agda.Builtins"
        ] ++ map (show . amiModule ) modImps]
  let impsCr = map mkImport imps
      exps = getExports modInfo
      cmod = mkModule (mkHsName1 $ show $ xmodName mod) exps impsCr cMetaDeclL funs
--  let hiImps = S.fromList imps
  return cmod

funsToCore :: Monad m => [Fun] -> FreshNameT m CExpr
funsToCore funs = do
  binds <- mapM funToBind funs
  let body = mkLetRec binds (mkInt opts 0)
  return body

buildCMetaDeclL :: [ADataTy] -> [CDeclMeta]
buildCMetaDeclL dts = catMaybes $ map f dts
    where f :: ADataTy -> Maybe CDeclMeta
          -- foreign/builtin datatypes are defined somewhere else. For normal datatypes, core name is always defined.
          f d@(ADataTy{xdatImplType = ADataImplNormal}) = Just $ mkMetaData (fromMaybe __IMPOSSIBLE__ $ xdatName d) (map g (xdatCons d))
          f _ = Nothing
          g :: ADataCon -> CDataCon
          g c@(ADataCon{}) =
                                -- can return Nothing for the tuple/record/() ctag, but should never happen
                              fromMaybe __IMPOSSIBLE__ $ mkMetaDataConFromCTag (xconCTag c)


funToBind :: Monad m => Fun -> FreshNameT m CBind
funToBind (Fun _ name mqname comment vars e) = do -- TODO what is mqname?
  e' <- exprToCore e
  let body = mkLam vars e'
  return $ mkBind1 name body
funToBind (CoreFun name _ _ crExpr _) = return $ mkBind1 name crExpr

exprToCore :: Monad m => Expr -> FreshNameT m CExpr
exprToCore (Var v)      = return $ mkVar v
exprToCore (Lit l)      = return $ litToCore l
exprToCore (Lam v body) = exprToCore body >>= return . mkLam [v]
exprToCore (Con ty con es) = do
    es' <- mapM exprToCore es
    return $ mkTagTup (xconCTag con) es'
exprToCore (App fv es)   = do
    es' <- mapM exprToCore es
    let fv' = mkVar fv
    return $ mkApp fv' es'
exprToCore (Case e brs) = do
    var <- freshLocalName
    (def, branches) <- branchesToCore brs
    let cas = mkCaseDflt (mkVar var) branches (Just def)
    e' <- exprToCore e
    return $ mkLet1Strict var e' cas
exprToCore (Let v e1 e2) = do
    e1' <- exprToCore e1
    e2' <- exprToCore e2
    return $ mkLet1Plain v e1' e2'
exprToCore UNIT         = return $ mkUnit opts
exprToCore IMPOSSIBLE   = return $ coreImpossible ""

branchesToCore :: Monad m => [Branch] -> FreshNameT m (CExpr, [CAlt])
branchesToCore brs = do
    let defs = filter isDefault brs
    def <- if null defs then return (coreImpossible "Default branch reached, but doesn't exit.") else let (Default x) = head defs in exprToCore x
    brs' <- mapM f brs

    return (def, concat brs')
    where
          f (Branch con _ vars e)  = do
            -- TODO can we do mkHsName [] "" here?
            let patFlds = [mkPatFldBind (mkHsName [] "", mkInt opts i) (mkBind1Nm1 v) | (i, v) <- zip [0..] vars]
            e' <- exprToCore e
            return [mkAlt (mkPatCon (xconCTag con) mkPatRestEmpty patFlds) e']
          f (Default e) = return []
          -- UHC resets the tags for some constructors, but only those wo are defined in the same module. So just set it anyway, to be safe.
          conSpecToTag (dt, ctor, tag) = mkCTag (mkHsName1 dt) (mkHsName1 $ (modNm dt) ++ "." ++ ctor) tag
          modNm s = reverse $ tail $ dropWhile (/= '.') $ reverse s
          isDefault (Default _) = True
          isDefault _ = False


litToCore :: Lit -> CExpr
-- should we put this into a let?
litToCore (LInt i) = mkApp (mkVar $ mkHsName ["UHC", "Agda", "Builtins"] "primIntegerToNat") [mkInteger opts i]
litToCore (LString s) = mkString opts s
litToCore (LChar c) = mkChar c
-- TODO this is just a dirty work around
litToCore (LFloat f) = mkApp (mkVar $ mkHsName ["UHC", "Agda", "Builtins"] "primMkFloat") [mkString opts (show f)]

coreImpossible :: String -> CExpr
coreImpossible msg = mkError opts $ "BUG! Impossible code reached. " ++ msg

