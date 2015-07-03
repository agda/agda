{-# LANGUAGE CPP, DoAndIfThenElse #-}

-- | Convert the AuxAST code to UHC Core code.
module Agda.Compiler.UHC.Core
  ( toCore
  , mkHsName
  , coreError
  , createMainModule
  ) where

import Data.List
import qualified Data.Map as M
import Data.Maybe (fromMaybe, catMaybes)
import qualified Data.Set as Set
#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative
#endif
import Control.Monad.State
import Control.Monad.Reader

import Agda.Interaction.Options
import Agda.TypeChecking.Monad
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Utils.Pretty

import Agda.Compiler.UHC.AuxAST
import Agda.Compiler.UHC.Naming
import Agda.Compiler.UHC.ModuleInfo

import Agda.Compiler.UHC.Bridge


#include "undefined.h"
import Agda.Utils.Impossible

opts :: EHCOpts
opts = defaultEHCOpts

-- stores tracing level
type ToCoreT m = FreshNameT (ReaderT Int m)

createMainModule :: AModuleInfo -> HsName -> CModule
createMainModule mainMod main = mkModule (mkHsName [] "Main") [] [mkImport $ mkHsName1 "UHC.Run", mkImport mainModAux] [] (mkMain main)
  where mainModAux = snd $ fromMaybe __IMPOSSIBLE__ $ mnameToCoreName (amifNameMp $ amiInterface mainMod) (amiModule mainMod)

getExports :: AModuleInfo -> [CExport]
getExports modInfo = map (mkExport . cnName) (expFuns ++ expDtFuns ++ expConFuns)
  where expFuns = getExportsFor EtFunction
        -- there is a function for each datatype, named as the datatype itself.
        -- This is used as type-dummy, returning always unit.
        -- We need to export those too.
        expDtFuns = getExportsFor EtDatatype
        -- and the constructor wrapper functions
        expConFuns = getExportsFor EtConstructor

        getExportsFor ty = let items = M.elems $ getNameMappingFor (amifNameMp $ amiInterface modInfo) ty
                            in filter needsExport items
        needsExport x = cnAgdaExported x


toCore :: AMod      -- ^ The current module to compile.
    -> AModuleInfo  -- ^ Info about current module.
    -> AModuleInterface -- ^ Transitive interface.
    -> [AModuleInfo] -- ^ Top level imports
    -> TCM CModule
toCore amod modInfo transModIface modImps = do

  traceLvl <- optUHCTraceLevel <$> commandLineOptions
  funs <- flip runReaderT traceLvl $ evalFreshNameT "nl.uu.agda.to_core" $ funsToCore (xmodFunDefs amod)

  let cMetaDeclL = buildCMetaDeclL (xmodDataTys amod)

  let imps = map mkHsName1
        ( Set.toList
        $ Set.insert "UHC.Base"
        $ Set.insert "UHC.Agda.Builtins"
        $ xmodCrImports amod
        ) ++ map (mnmToCrNm . amiModule) modImps
  let impsCr = map mkImport imps
      exps = getExports modInfo
      crModNm = mnmToCrNm $ xmodName amod
      cmod = mkModule crModNm exps impsCr cMetaDeclL funs
  return cmod
  where mnmToCrNm :: ModuleName -> HsName
        mnmToCrNm mnm = snd (fromMaybe __IMPOSSIBLE__ $ mnameToCoreName (amifNameMp transModIface) mnm)

funsToCore :: Monad m => [Fun] -> ToCoreT m CExpr
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
          -- mkMetaDataConFromCTag can return Nothing for the tuple/record/() ctag, but should never happen
          g c@(ADataCon{}) = fromMaybe __IMPOSSIBLE__ $ mkMetaDataConFromCTag (xconCTag c)


funToBind :: Monad m => Fun -> ToCoreT m CBind
funToBind (Fun _ name _ _ vars e) = do
  e' <- exprToCore e

  body <- coreTrace1 5 ("Eval fun: " ++ show name) $ mkLam vars e'

  ifTracing 10
    (do
      vars' <- replicateM (length vars) freshLocalName

      let body' = (mkApp body
            [coreTrace ("Eval arg: " ++ show name ++ " :: " ++ show i) (mkVar v)
                | (v, i) <- zip vars' [(0 :: Integer)..]
            ])
      return $ mkBind1 name $ mkLam vars' body'
      )
    (return $ mkBind1 name body)
funToBind (CoreFun name _ _ crExpr) = return $ mkBind1 name crExpr

exprToCore :: Monad m => Expr -> ToCoreT m CExpr
exprToCore (Var v)      = return $ mkVar v
exprToCore (Lit l)      = return $ litToCore l
exprToCore (Lam v body) = exprToCore body >>= return . mkLam [v]
exprToCore (Con _ con es) = do
    es' <- mapM exprToCore es
    return $ mkTagTup (xconCTag con) es'
exprToCore (App f es)   = do
    f' <- exprToCore f
    es' <- mapM exprToCore es
    return $ mkApp f' es'
exprToCore (Case e brs def (CTCon dt)) = do
  caseScr <- freshLocalName
  defVar <- freshLocalName
  def' <- exprToCore def

  branches <- branchesToCore brs
  defBranches <- defaultBranches dt brs (mkVar defVar)
  let cas = mkCase (mkVar caseScr) (branches ++ defBranches)
  e' <- exprToCore e
  return $ mkLet1Plain defVar def' (mkLet1Strict caseScr e' cas)
-- cases on literals
exprToCore (Case e brs def ct) = do
  e' <- exprToCore e
  var <- freshLocalName
  def' <- exprToCore def

  css <- buildPrimCases (eq ct) (mkVar var) brs (getLit ct) def'
  return $ mkLet1Strict var e' css
  where eq :: CaseType -> CExpr
        eq CTChar = mkVar $ mkHsName ["UHC", "Agda", "Builtins"] "primCharEquality"
        eq CTString = mkVar $ mkHsName ["UHC", "Agda", "Builtins"] "primStringEquality"
        eq _ = __IMPOSSIBLE__
        getLit :: CaseType -> Branch -> CExpr
        getLit CTChar   = mkChar . brChar
        getLit CTString = mkString opts . brStr
        getLit _ = __IMPOSSIBLE__
exprToCore (Let v e1 e2) = do
    e1' <- exprToCore e1
    e2' <- exprToCore e2
    return $ mkLet1Plain v e1' e2'
exprToCore UNIT         = return $ mkUnit opts
exprToCore (Error e)    = return $ coreError e

buildPrimCases :: Monad m
    => CExpr -- ^ equality function
    -> CExpr    -- ^ case scrutinee (in WHNF)
    -> [Branch]
    -> (Branch -> CExpr) -- extract literal expr from branch
    -> CExpr    -- ^ default value
    -> ToCoreT m CExpr
buildPrimCases _ _ [] _ def = return def
buildPrimCases eq scr (b:brs) getLit def = do
    var <- freshLocalName
    e' <- exprToCore (brExpr b)
    rec' <- buildPrimCases eq scr brs getLit def

    let eqTest = mkApp eq [scr, getLit b]

    return $ mkLet1Strict var eqTest (mkIfThenElse (mkVar var) e' rec')

-- move to UHC Core API
mkIfThenElse :: CExpr -> CExpr -> CExpr -> CExpr
mkIfThenElse c t e = mkCase c [b1, b2]
  where b1 = mkAlt (mkPatCon (ctagTrue opts) mkPatRestEmpty []) t
        b2 = mkAlt (mkPatCon (ctagFalse opts) mkPatRestEmpty []) e

branchesToCore :: Monad m => [Branch] -> ToCoreT m [CAlt]
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
defaultBranches :: Monad m => ADataTy -> [Branch] -> CExpr -> ToCoreT m [CAlt]
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
litToCore (LInt i) = mkApp (mkVar $ mkHsName ["UHC", "Agda", "Builtins"] "primIntegerToNat") [mkInteger opts i]
litToCore (LString s) = mkString opts s
litToCore (LChar c) = mkChar c
-- TODO this is just a dirty work around
litToCore (LFloat f) = mkApp (mkVar $ mkHsName ["UHC", "Agda", "Builtins"] "primMkFloat") [mkString opts (show f)]
litToCore (LQName q) = mkApp (mkVar $ mkHsName ["UHC", "Agda", "Builtins"] "primMkQName")
                             [mkInteger opts n, mkInteger opts m, mkString opts $ prettyShow q]
  where NameId n m = nameId $ qnameName q

ifTracing :: Monad m => Int -> ToCoreT m a -> ToCoreT m a -> ToCoreT m a
ifTracing lvl i e = do
  t <- ask
  if lvl <= t then i else e

coreTrace1 :: Monad m => Int -> String -> CExpr ->  ToCoreT m CExpr
coreTrace1 lvl msg e = do
  t <- ask
  if lvl <= t then
    return $ coreTrace msg e
  else return e

coreTrace :: String -> CExpr -> CExpr
coreTrace msg x = mkApp (mkVar $ mkHsName ["UHC", "Agda", "Builtins"] "primTrace") [mkString opts msg, x]

coreError :: String -> CExpr
coreError msg = mkError opts $ "Fatal error: " ++ msg
