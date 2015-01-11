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


createMainModule :: AModuleInfo -> HsName -> CModule
createMainModule mainMod main = mkModule (mkHsName [] "Main") [] [mkImport $ mkHsName1 "UHC.Run", mkImport mainMod'] [] (mkMain main)
  where mainMod' = snd $ fromMaybe __IMPOSSIBLE__ $ mnameToCoreName (amiCurNameMp mainMod) (amiModule mainMod)

getExports :: AModuleInfo -> [CExport]
getExports modInfo = map (mkExport . cnName) (expFuns ++ expDtFuns ++ expConFuns)
  where expFuns = getExportsFor EtFunction
        -- there is a function for each datatype, named as the datatype itself.
        -- This is used as type-dummy, returning always unit.
        -- We need to export those too.
        expDtFuns = getExportsFor EtDatatype
        -- and the constructor wrapper functions
        expConFuns = getExportsFor EtConstructor

        getExportsFor ty = let items = M.elems $ getNameMappingFor (amiCurNameMp modInfo) ty
                            in filter needsExport items
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
        ]] ++ map (mnmToCrNm . amiModule) modImps
  let impsCr = map mkImport imps
      exps = getExports modInfo
      crModNm = mnmToCrNm $ xmodName mod
      cmod = mkModule crModNm exps impsCr cMetaDeclL funs
--  let hiImps = S.fromList imps
  return cmod
  where mnmToCrNm :: ModuleName -> HsName
        mnmToCrNm mnm = snd (fromMaybe __IMPOSSIBLE__ $ mnameToCoreName (amifNameMp $ amiInterface modInfo) mnm)

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
exprToCore (Case e brs def CTChar) = do
  e' <- exprToCore e
  var <- freshLocalName
  def' <- case def of
        Nothing -> return $ mkError opts "Non-exhaustive case didn't match any alternative."
        Just x -> exprToCore x

  css <- buildPrimCases eq (mkVar var) brs def'
  return $ mkLet1Strict var e' css
  where eq = mkVar $ mkHsName ["UHC", "Agda", "Builtins"] "primCharEquality"
exprToCore (Case e brs def (CTCon dt)) = do
  caseScr <- freshLocalName
  defVar <- freshLocalName
  def <- case def of
        Nothing -> return $ mkError opts "Non-exhaustive case didn't match any alternative."
        Just x -> exprToCore x


  branches <- branchesToCore brs
  defBranches <- defaultBranches dt brs (mkVar defVar)
  let cas = mkCase (mkVar caseScr) (branches ++ defBranches)
  e' <- exprToCore e
  return $ mkLet1Plain defVar def (mkLet1Strict caseScr e' cas)
exprToCore (Let v e1 e2) = do
    e1' <- exprToCore e1
    e2' <- exprToCore e2
    return $ mkLet1Plain v e1' e2'
exprToCore UNIT         = return $ mkUnit opts
exprToCore IMPOSSIBLE   = return $ coreImpossible ""

buildPrimCases :: Monad m
    => CExpr -- ^ equality function
    -> CExpr    -- ^ case scrutinee (in WHNF)
    -> [Branch]
    -> CExpr    -- ^ default value
    -> FreshNameT m CExpr
buildPrimCases _ _ [] def = return def
buildPrimCases eq scr (b:brs) def = do
    var <- freshLocalName
    e' <- exprToCore (brExpr b)
    rec' <- buildPrimCases eq scr brs def

    let eqTest = mkApp eq [scr, mkChar (brChar b)]

    return $ mkLet1Strict var eqTest (mkIfThenElse (mkVar var) e' rec')

-- move to UHC Core API
mkIfThenElse :: CExpr -> CExpr -> CExpr -> CExpr
mkIfThenElse c t e = mkCase c [b1, b2]
  where b1 = mkAlt (mkPatCon (ctagTrue opts) mkPatRestEmpty []) t
        b2 = mkAlt (mkPatCon (ctagFalse opts) mkPatRestEmpty []) e

branchesToCore :: Monad m => [Branch] -> FreshNameT m [CAlt]
branchesToCore brs = do
    brs' <- mapM f brs
    return brs'
    where
          f (BrCon con _ vars e)  = do
            -- TODO can we do mkHsName [] "" here?
            let patFlds = [mkPatFldBind (mkHsName [] "", mkInt opts i) (mkBind1Nm1 v) | (i, v) <- zip [0..] vars]
            e' <- exprToCore e
            return $ mkAlt (mkPatCon (xconCTag con) mkPatRestEmpty patFlds) e'
          f _ = __IMPOSSIBLE__

-- | Constructs an alternative for all constructors not explicitly matched by a branch.
defaultBranches :: Monad m => ADataTy -> [Branch] -> CExpr -> FreshNameT m [CAlt]
defaultBranches dt brs def = mapM mkAlt' missingCons
  where missingCons = (map xconCTag $ xdatCons dt) \\ (map (xconCTag . brCon) brs)
        mkAlt' ctg = do
                patFlds <- mkPatFlds ctg
                -- TODO investigate if we could use PatRest_Var instead for this
                return $ mkAlt (mkPatCon ctg mkPatRestEmpty patFlds) def
        mkPatFlds ctg = do
                let ar = getCTagArity ctg
                dummyVars <- replicateM ar freshLocalName
                return [mkPatFldBind (mkHsName [] "", mkInt opts i) (mkBind1Nm1 v) | (i, v) <- zip [0..] dummyVars]


litToCore :: Lit -> CExpr
-- should we put this into a let?
litToCore (LInt i) = mkApp (mkVar $ mkHsName ["UHC", "Agda", "Builtins"] "primIntegerToNat") [mkInteger opts i]
litToCore (LString s) = mkString opts s
litToCore (LChar c) = mkChar c
-- TODO this is just a dirty work around
litToCore (LFloat f) = mkApp (mkVar $ mkHsName ["UHC", "Agda", "Builtins"] "primMkFloat") [mkString opts (show f)]

coreImpossible :: String -> CExpr
coreImpossible msg = mkError opts $ "BUG! Impossible code reached. " ++ msg

