{-# LANGUAGE CPP, DoAndIfThenElse #-}

-- | Convert from Agda's internal representation to our auxiliary AST.
--
--
-- The coinduction kit is translated the same way as in MAlonzo:
-- flat = id
-- sharp = id
-- -> There is no runtime representation of Coinductive values.
module Agda.Compiler.UHC.FromAgda where

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative
#endif

import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M
import Data.Maybe
import Data.Either

import Agda.Syntax.Internal hiding (Term(..))
import qualified Agda.Syntax.Internal as I
import qualified Agda.Syntax.Literal  as TL
import qualified Agda.Syntax.Treeless as C
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.Utils.List
import qualified Agda.Utils.HashMap as HMap

import Agda.Compiler.ToTreeless
import Agda.Compiler.UHC.Pragmas.Base
import Agda.Compiler.UHC.Pragmas.Parse (coreExprToCExpr)
import Agda.Compiler.UHC.AuxAST as A
import Agda.Compiler.UHC.AuxASTUtil
import Agda.Compiler.UHC.CompileState
import Agda.Compiler.UHC.ModuleInfo
import Agda.Compiler.UHC.Primitives
import Agda.Compiler.UHC.Core
import Agda.Compiler.UHC.Naming
import Agda.Compiler.UHC.MagicTypes

import Agda.Compiler.UHC.Bridge as CA

#include "undefined.h"
import Agda.Utils.Impossible

-- | Convert from Agda's internal representation to our auxiliary AST.
fromAgdaModule :: ModuleName
    -> [AModuleInfo]     -- Module info of imported modules.
    -> AModuleInterface  -- Transitive module interface of all dependencies.
    -> Interface         -- interface to compile
    -> (AMod -> CompileT TCM a) -- continuation, normally program transforms
    -> TCM (a, AModuleInfo)
fromAgdaModule modNm curModImps transModIface iface cont = do
  kit <- coinductionKit

  let defs = HMap.toList $ sigDefinitions $ iSignature iface

  reportSLn "uhc" 15 "Building name database..."
  defNames <- collectNames defs
  nameMp <- assignCoreNames modNm defNames
  reportSLn "uhc" 25 $ "NameMap for " ++ show modNm ++ ":\n" ++ show nameMp


  (mod', modInfo') <- runCompileT kit modNm curModImps transModIface nameMp (do
    lift $ reportSLn "uhc" 10 "Translate datatypes..."
    -- Translate and add datatype information
    dats <- translateDataTypes defs
    let conMp = buildConMp dats
    addConMap conMp

    lift $ reportSLn "uhc" 25 $ "Constructor Map for " ++ show modNm ++ ":\n" ++ show conMp


    funs <- evalFreshNameT "nl.uu.agda.from-agda" (catMaybes <$> mapM translateDefn defs)

    -- additional core/HS imports for the FFI
    additionalImports <- lift getHaskellImportsUHC
    let amod = AMod { xmodName = modNm
                  , xmodFunDefs = funs
                  , xmodDataTys = dats
                  , xmodCrImports = additionalImports
                  }
    cont amod
    )

  return (mod', modInfo')
  where buildConMp :: [ADataTy] -> M.Map QName AConInfo
        buildConMp dts = M.fromList $ concatMap datToConInfo dts
        datToConInfo :: ADataTy -> [(QName, AConInfo)]
        datToConInfo dt = [(xconQName con, AConInfo dt con) | con <- xdatCons dt]

-- | Collect module-level names.
collectNames :: [(QName, Definition)] -> TCM [AgdaName]
collectNames defs = do
  return $ catMaybes $ map collectName defs
  where collectName :: (QName, Definition) -> Maybe AgdaName
        collectName (qnm, def) =
            let ty = case theDef def of
                    (Datatype {}) -> EtDatatype
                    (Function {}) -> EtFunction
                    (Constructor {}) -> EtConstructor
                    (Record {}) -> EtConstructor
                    (Axiom {})  -> EtFunction
                    (Primitive {}) -> EtFunction
                isForeign = isJust $ compiledCore $ defCompiledRep def
            -- builtin/foreign constructors already have a core-level representation, so we don't need any fresh names
            -- but for the datatypes themselves we still want to create the type-dummy function
            in case theDef def of
                  _ | ty == EtConstructor && isForeign -> Nothing
                  _ | otherwise -> Just AgdaName
                        { anName = qnm
                        , anType = ty
                        , anNeedsAgdaExport = True -- TODO, only set this to true for things which are actually exported
                        , anForceName = Nothing -- TODO add pragma to force name
                        }

-- | Collects all datatype information for non-instantiated datatypes.
translateDataTypes :: [(QName, Definition)] -> CompileT TCM [ADataTy]
translateDataTypes defs = do
  kit <- getCoinductionKit
  -- first, collect all constructors
  -- Right elements are foreign datatype constructors,
  -- Lefts are normally compiled Agda datatype constructors.
  constrMp <- M.unionsWith (++)
    <$> mapM (\(n, def) ->
        case theDef def of
            d@(Constructor {}) -> do
                let isForeign = compiledCore $ defCompiledRep def
                arity' <- lift $ (fst <$> conArityAndPars n)
                let conFun = ADataCon n
                con <- case isForeign of
                    (Just (CrConstr crcon)) -> return $ Right (conFun $ coreConstrToCTag crcon arity')
                    (Nothing)   -> do
                        conCrNm <- getCoreName1 n
                        return $ Left (\tyCrNm tag -> conFun (mkCTag tyCrNm conCrNm tag arity'))
                    _ -> __IMPOSSIBLE__
                return $ M.singleton (conData d) [con]
            _ -> return M.empty
        ) defs

  -- now extract all datatypes, and use the constructor info
  -- collected before
  let handleDataRecDef = (\n def -> do
            let isForeign = compiledCore $ defCompiledRep def
            let cons = M.findWithDefault [] n constrMp
            case (isForeign, partitionEithers cons) of
              (Just (CrType crty), ([], cons')) -> do -- foreign datatypes (COMPILED_DATA_UHC)
                    let (tyNm, impl) = case crty of
                                CTMagic mgcNm -> let tyNm' = fst $ getMagicTypes M.! mgcNm
                                        in (tyNm', ADataImplMagic mgcNm)
                                CTNormal tyNm' -> (Just $ mkHsName1 tyNm', ADataImplForeign)
                    return $ Just (ADataTy tyNm n cons' impl)
              (Nothing, (cons', [])) -> do
                    tyCrNm <- getCoreName1 n
                    -- build ctags, assign tag numbers
                    let cons'' = map (\((conFun), i) -> conFun tyCrNm i) (zip cons' [0..])
                    return $ Just (ADataTy (Just tyCrNm) n cons'' ADataImplNormal)
              _ -> __IMPOSSIBLE__ -- datatype is builtin <=> all constructors have to be builtin
              )

  catMaybes <$> mapM
    (\(n, def) -> case theDef def of
        (Record{}) | Just n /= (nameOfInf <$> kit)
                -> handleDataRecDef n def
        -- coinduction kit gets erased in the translation to AuxAST
        (Datatype {})
                -> handleDataRecDef n def
        _       -> return Nothing
    ) defs


-- | Translate an Agda definition to an UHC Core function where applicable
translateDefn :: (QName, Definition) -> FreshNameT (CompileT TCM) (Maybe Fun)
translateDefn (n, defini) = do
  nmSizeUniv <- fmap (\(I.Def nm []) -> nm)
    <$> (lift . lift) (getBuiltin' builtinSizeUniv)

  crName <- lift $ getCoreName n
  let crRep = compiledCore $ defCompiledRep defini
  kit <- lift getCoinductionKit
  case theDef defini of
    d@(Datatype {}) -> do -- become functions returning unit
        vars <- replicateM (dataPars d + dataIxs d) freshLocalName
        return . return $ Fun True (fromMaybe __IMPOSSIBLE__ crName) (Just n) ("datatype: " ++ show n) vars UNIT
    (Function{}) | Just n == (nameOfFlat <$> kit) -> do
        Just <$> mkIdentityFun n "coind-flat" 0
    (Function{}) | Just n == nmSizeUniv -> do
        return $ Just $ Fun False (fromMaybe __IMPOSSIBLE__ crName) (Just n) ("size-univ") [] UNIT
    f@(Function{}) | otherwise -> do
        let ty    = (defType defini)
        lift . lift $ reportSDoc "uhc.fromagda" 5 $ text "compiling fun:" <+> prettyTCM n
        lift . lift $ reportSDoc "uhc.fromagda" 15 $ text "type:" <+> (text . show) ty
        let cc = fromMaybe __IMPOSSIBLE__ $ funCompiled f

        funBody <- runSubst . substTerm =<< (lift . lift) (ccToTreeless n cc)

        return $ Just $ Fun False (fromMaybe __IMPOSSIBLE__ crName) (Just n) ("function: " ++ show n) [] funBody

    Constructor{} | Just n == (nameOfSharp <$> kit) -> do
        Just <$> mkIdentityFun n "coind-sharp" 0

    (Constructor{}) | otherwise -> do -- become functions returning a constructor with their tag

        case crName of
          (Just _) -> do
                    conInfo <- lift $ getConstrInfo n
                    let conCon = aciDataCon conInfo
                        arity' = xconArity conCon

                    vars <- replicateM arity' freshLocalName
                    return $ Just $ Fun True (ctagCtorName $ xconCTag conCon) (Just n)
                            ("constructor: " ++ show n) vars (Con (aciDataType conInfo) conCon (map Var vars))
          Nothing -> return Nothing -- either foreign or builtin type. We can just assume existence of the wrapper functions then.

    r@(Record{}) -> do
        vars <- replicateM (recPars r) freshLocalName
        return . return $ Fun True (fromMaybe __IMPOSSIBLE__ crName) (Just n) ("record: " ++ show n) vars UNIT
    (Axiom{}) -> do -- Axioms get their code from COMPILED_UHC pragmas
        case crRep of
            Nothing -> return . return $ CoreFun (fromMaybe __IMPOSSIBLE__ crName) (Just n) ("AXIOM_UNDEFINED: " ++ show n)
                (coreImpossible $ "Axiom " ++ show n ++ " used but has no computation.")
            Just (CrDefn x) -> do
                        x' <- case coreExprToCExpr x of
                                -- This can only happen if an *.agdai file was generated by an Agda version
                                -- without UHC support enabled.
                                Left err -> internalError $ "Invalid COMPILED_UHC pragma value: " ++ err
                                Right y -> return y
                        return . return $ CoreFun (fromMaybe __IMPOSSIBLE__ crName) (Just n) ("COMPILED_UHC: " ++ show n) x'
            _ -> __IMPOSSIBLE__

    p@(Primitive{}) -> do -- Primitives use primitive functions from UHC.Agda.Builtins of the same name.

      case primName p `M.lookup` primFunctions of
        Nothing     -> internalError $ "Primitive " ++ show (primName p) ++ " declared, but no such primitive exists."
        (Just expr) -> do
                expr' <- lift expr
                return $ Just $ CoreFun (fromMaybe __IMPOSSIBLE__ crName) (Just n) ("primitive: " ++ primName p) expr'
  where
    -- | Produces an identity function, optionally ignoring the first n arguments.
    mkIdentityFun :: Monad m => QName
        -> String -- ^ comment
        -> Int      -- ^ How many arguments to ignore.
        -> FreshNameT (CompileT m) Fun
    mkIdentityFun nm comment ignArgs = do
        crName <- lift $ getCoreName1 nm
        xs <- replicateM (ignArgs + 1) freshLocalName
        return $ Fun False crName (Just n) comment xs (Var $ last xs)


runSubst :: NM a -> FreshNameT (CompileT TCM) a
runSubst r = r `runReaderT` (NMEnv [])

data NMEnv = NMEnv
  { nmEnv :: [HsName] -- maps de-bruijn indices to names
  }

type NM = ReaderT NMEnv (FreshNameT (CompileT TCM))


addToEnv :: [HsName] -> NM a -> NM a
addToEnv nms cont =
  local (\e -> e { nmEnv = nms ++ (nmEnv e) }) cont

-- | Translate the actual Agda terms, with an environment of all the bound variables
--   from patternmatching. Agda terms are in de Bruijn so we just check the new
--   names in the position.
substTerm :: C.TTerm -> NM A.Expr
substTerm term = case term of
    C.TVar x -> do
      nm <- fromMaybe __IMPOSSIBLE__ . (!!! x) <$> asks nmEnv
      return $ A.Var nm
    C.TDef nm -> do
      nm' <- lift . lift $ getCoreName1 nm
      return $ A.Var nm'
    C.TApp t xs -> do
      A.apps <$> substTerm t <*> mapM substTerm xs
    C.TLam t -> do
       name <- lift freshLocalName
       addToEnv [name] $ do
         A.Lam name <$> substTerm t
    C.TLit l -> return $ Lit (substLit l)
    C.TCon c -> do
        con <- lift . lift $ getConstrFun c
        return $ A.Var con
    C.TLet x body -> do
        nm <- lift freshLocalName
        A.Let nm
            <$> substTerm x
            <*> addToEnv [nm] (substTerm body)
    C.TCase sc ct def alts -> do
        A.Case
          <$> substTerm sc
          <*> mapM substAlt alts
          <*> substTerm def
          <*> mapCaseType ct
      where mapCaseType :: C.CaseType -> NM A.CaseType
            mapCaseType C.CTChar = return $ A.CTChar
            mapCaseType C.CTString = return $ A.CTString
            mapCaseType (C.CTData _) = do
                let (C.TACon {C.aCon = conNm}) = head alts
                di <- aciDataType <$> (lift . lift) (getConstrInfo conNm)
                return $ A.CTCon di
            substAlt :: C.TAlt -> NM A.Branch
            substAlt a@(C.TAChar {}) = A.BrChar (C.aChar a) <$> substTerm (C.aBody a)
            substAlt a@(C.TAString {}) = A.BrString (C.aStr a) <$> substTerm (C.aBody a)
            substAlt a@(C.TACon {}) = do
                conInfo <- aciDataCon <$> (lift . lift) (getConstrInfo $ C.aCon a)
                let ar = xconArity conInfo
                vars <- lift $ replicateM ar freshLocalName
                body <- addToEnv (reverse vars) (substTerm $ C.aBody a)
                return $ A.BrCon conInfo (C.aCon a) vars body
    C.TPi _ _ -> __IMPOSSIBLE__
    C.TUnit -> return UNIT
    C.TSort -> return UNIT
    C.TErased -> return UNIT
    C.TError _ -> return IMPOSSIBLE -- TODO translate errors proberly here

-- | Translate Agda literals to our AUX definition
substLit :: TL.Literal -> Lit
substLit lit = case lit of
  TL.LitInt    _ i -> LInt i
  TL.LitString _ s -> LString s
  TL.LitChar   _ c -> LChar c
  TL.LitFloat  _ f -> LFloat f
  TL.LitQName  _ q -> LQName q
