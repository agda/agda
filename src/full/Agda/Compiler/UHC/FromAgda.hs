{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP, DoAndIfThenElse #-}

-- | Convert from Agda's internal representation to our auxiliary AST.
--
--
-- The coinduction kit is translated the same way as in MAlonzo:
-- flat = id
-- sharp = id
-- -> There is no runtime representation of Coinductive values.
module Agda.Compiler.UHC.FromAgda where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import qualified Data.Map as M
import Data.Maybe
import Data.Either

import Agda.Syntax.Common
import Agda.Syntax.Internal hiding (Term(..))
import qualified Agda.Syntax.Internal as T
import qualified Agda.Syntax.Literal  as TL
import qualified Agda.TypeChecking.CompiledClause as CC
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Level (reallyUnLevelView)
import qualified Agda.TypeChecking.Substitute as S
import Agda.TypeChecking.Pretty
import Agda.Utils.List
import Agda.TypeChecking.Monad.Builtin

import Agda.Compiler.UHC.Pragmas.Base
import Agda.Compiler.UHC.AuxAST
import Agda.Compiler.UHC.AuxASTUtil
import Agda.Compiler.UHC.CompileState
import Agda.Compiler.UHC.ModuleInfo
import Agda.Compiler.UHC.Primitives
import Agda.Compiler.UHC.Core
import Agda.Compiler.UHC.Naming

import Agda.Compiler.UHC.Bridge as CA

#include "undefined.h"
import Agda.Utils.Impossible

-- | Convert from Agda's internal representation to our auxiliary AST.
fromAgdaModule :: ModuleName
    -> [AModuleInfo]     -- Module info of imported modules.
    -> AModuleInterface  -- Transitive module interface of all dependencies.
    -> [(QName, Definition)]
    -> (AMod -> CompileT TCM a) -- continuation, normally program transforms
    -> TCM (a, AModuleInfo)
fromAgdaModule modNm curModImps transModIface defs cont = do
  kit <- coinductionKit

  let conInstMp = getInstantiationMap defs
  reportSLn "uhc" 25 $ "Instantiation Map for " ++ show modNm ++ ":\n" ++ show conInstMp

  reportSLn "uhc" 15 "Building name database..."
  defNames <- collectNames conInstMp defs
  nameMp <- assignCoreNames modNm defNames
  reportSLn "uhc" 25 $ "NameMap for " ++ show modNm ++ ":\n" ++ show nameMp


  (mod', modInfo') <- runCompileT kit modNm curModImps transModIface nameMp conInstMp (do
    lift $ reportSLn "uhc" 10 "Translate datatypes..."
    -- Translate and add datatype information
    dats <- translateDataTypes defs
    let conMp = buildConMp dats
    addConMap conMp

    lift $ reportSLn "uhc" 25 $ "Constructor Map for " ++ show modNm ++ ":\n" ++ show conMp


    funs <- evalFreshNameT "nl.uu.agda.from-agda" (catMaybes <$> mapM translateDefn defs)

    let amod = AMod { xmodName = modNm
                  , xmodFunDefs = funs
                  , xmodDataTys = dats
                  }
    cont amod
    )

  return (mod', modInfo')
  where buildConMp :: [ADataTy] -> M.Map QName AConInfo
        buildConMp dts = M.fromList $ concatMap datToConInfo dts
        datToConInfo :: ADataTy -> [(QName, AConInfo)]
        datToConInfo dt = [(xconQName con, AConInfo dt con) | con <- xdatCons dt]

-- | Collect module-level names.
collectNames :: ConInstMp -> [(QName, Definition)] -> TCM [AgdaName]
collectNames conInstMp defs = do
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
                  (Constructor {}) | (M.findWithDefault __IMPOSSIBLE__ qnm conInstMp) /= qnm -> Nothing -- constructor is instantiated
                  _ | otherwise -> Just AgdaName
                        { anName = qnm
                        , anType = ty
                        , anNeedsAgdaExport = True -- TODO, only set this to true for things which are actually exported
                        , anForceName = Nothing -- TODO add pragma to force name
                        }

-- | Computes the constructor instantiation map.
getInstantiationMap :: [(QName, Definition)] -> ConInstMp
getInstantiationMap defs =
  M.unions $ map (\(n, def) ->
        case theDef def of
            Constructor {conSrcCon = srcCon} -> M.singleton n (conName srcCon)
            Record {recConHead = conHd} -> M.singleton n (conName conHd)
            _ -> M.empty
        ) defs


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
                let foreign = compiledCore $ defCompiledRep def
                arity' <- lift $ (fst <$> conArityAndPars n)
                let conFun = ADataCon n
                con <- case foreign of
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
            let foreign = compiledCore $ defCompiledRep def
            let cons = M.findWithDefault [] n constrMp
            case (foreign, partitionEithers cons) of
              (Just (CrType crty), ([], cons')) -> do -- foreign datatypes (COMPILED_CORE_DATA)
                    let (tyNm, impl) = case crty of
                                CTMagic tyNm' nm -> (tyNm', ADataImplMagic nm)
                                CTNormal tyNm' -> (tyNm', ADataImplForeign)
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
        x | isDtInstantiated x -> do
                    lift $ reportSLn "uhc.fromAgda" 30 $ "Datatype " ++ show n ++ " is instantiated, skipping it."
                    return Nothing
        (Record{}) | Just n /= (nameOfInf <$> kit)
                -> handleDataRecDef n def
        -- coinduction kit gets erased in the translation to AuxAST
        (Datatype {})
                -> handleDataRecDef n def
        _       -> return Nothing
    ) defs


isDtInstantiated :: Defn -> Bool
isDtInstantiated (Datatype {dataClause = Just _}) = True
isDtInstantiated (Record {recClause = Just _}) = True
isDtInstantiated _ = False


-- | Translate an Agda definition to an UHC Core function where applicable
translateDefn :: (QName, Definition) -> FreshNameT (CompileT TCM) (Maybe Fun)
translateDefn (n, defini) = do
  crName <- lift $ getCoreName n
  let crRep = compiledCore $ defCompiledRep defini
  kit <- lift getCoinductionKit
  case theDef defini of
    d@(Datatype {}) -> do -- become functions returning unit
        vars <- replicateM (dataPars d + dataIxs d) freshLocalName
        return . return $ Fun True (fromMaybe __IMPOSSIBLE__ crName) (Just n) ("datatype: " ++ show n) vars UNIT
    (Function{}) | Just n == (nameOfFlat <$> kit) -> do
        -- ignore the two type arguments
        Just <$> mkIdentityFun n "coind-flat" 2
    f@(Function{}) | otherwise -> do
        let projArgs = projectionArgs f
            cc       = fromMaybe __IMPOSSIBLE__ $ funCompiled f
        let ccs = reverseCCBody projArgs cc
        let clens = map (length . clausePats) (funClauses f)
            len   = minimum clens
            ty    = (defType defini)
        coindcs <- lift $ removeCoindCopatterns ccs
        lift . lift $ reportSDoc "uhc.fromagda" 5 $ text "compiling fun:" <+> prettyTCM n
        lift . lift $ reportSDoc "uhc.fromagda" 5 $ text "lens:" <+> (text . show) (len, clens)
        lift . lift $ reportSDoc "uhc.fromagda" 15 $ text "pats:" <+> (text . show) (map clausePats
                    $ funClauses f)
        lift . lift $ reportSDoc "uhc.fromagda" 15 $ text "type:" <+> (text . show) ty

        lift . lift $ reportSDoc "uhc.fromagda" 15 $ text "ccs: " <+> (text . show) ccs
        lift . lift $ reportSDoc "uhc.fromagda" 15 $ text "coindCC: " <+> (text . show) coindcs

        return <$> compileClauses n len projArgs coindcs

    Constructor{} | Just n == (nameOfSharp <$> kit) -> do
        Just <$> mkIdentityFun n "coind-sharp" 0

    (Constructor{}) | otherwise -> do -- become functions returning a constructor with their tag

        case crName of
          (Just _) -> do
                -- check if the constructor is in an instantiated module
                -- There will be no constructor info entry, if it is indeed an instantiated constructor.
                isInst <- lift $ isConstrInstantiated n
                case isInst of
                  True -> return Nothing -- we will directly call the proper ctor
                  False -> do
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
    (Axiom{}) -> do -- Axioms get their code from COMPILED_CORE pragmas
        case crRep of
            Nothing -> return . return $ CoreFun (fromMaybe __IMPOSSIBLE__ crName) (Just n) ("AXIOM_UNDEFINED: " ++ show n)
                (coreImpossible $ "Axiom " ++ show n ++ " used but has no computation.")
            Just (CrDefn x)  -> return . return $ CoreFun (fromMaybe __IMPOSSIBLE__ crName) (Just n) ("COMPILED_CORE: " ++ show n) x
            _       -> internalError "Compiled core must be def, something went wrong."
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


-- | Adds the offset from the projection args to all indexes.
-- The de-Bruijn indices in the function body are converted
-- here to de-Bruin levels.
reverseCCBody :: Int -> CC.CompiledClauses -> CC.CompiledClauses
reverseCCBody c cc = case cc of
  CC.Case n (CC.Branches cbr lbr cabr) -> CC.Case (c+n)
      $ CC.Branches (M.map (fmap $ reverseCCBody c) cbr)
        (M.map (reverseCCBody c) lbr)
        (fmap  (reverseCCBody c) cabr)
  CC.Done i t -> CC.Done i (S.applySubst
                              (S.parallelS $ map (flip T.Var []) $
                                 reverse $ take (length i) [c..])
                              t)
  CC.Fail     -> CC.Fail

-- | Coinduction is now implemented using Copatterns. We don't properly
-- support copatterns; for the time being, just drop the Coinduction
-- cases on Infinity / flat constructor.
removeCoindCopatterns :: CC.CompiledClauses -> CompileT TCM CC.CompiledClauses
removeCoindCopatterns cc = do

  flatName <- fmap nameOfFlat <$> getCoinductionKit

  case flatName of
    Just x  -> return $ go x cc
    Nothing -> return cc
  where go :: QName -> CC.CompiledClauses -> CC.CompiledClauses
        go flat (CC.Case n (CC.Branches cbr lbr cabr)) =
                case flat `M.lookup` cbr of
                    (Just flatCon) -> go flat $ CC.content flatCon
                    Nothing -> CC.Case n $ CC.Branches
                            (fmap (fmap (go flat)) cbr)
                            (fmap (go flat) lbr)
                            (fmap (go flat) cabr)
        go _ x = x

-- | Translate from Agda's desugared pattern matching (CompiledClauses) to our AuxAST.
--   This is all done by magic. It uses 'substTerm' to translate the actual
--   terms when the cases have been gone through.
--   The case expressions that we get use de Bruijn indices that change after
--   each case in the following way.
--   Say we have this pattern:
--
-- > f (X x y) (Y z) = term
--
--   Initially, the variables have these indexes:
--
-- > f 0@(X x y) 1@(Y z) = term
--
--   The first case will be on @0@, and the variables bound inside the @X@
--   pattern will replace the outer index, so we get something like this:
--
-- > f 0 2@(Y z) = case 0 of X 0 1 -> term
--
--   Notice how @(Y z)@ now has index @2@.
--   Then the second pattern is desugared in the same way:
--
-- > f 0 2 = case 0 of X 0 1 -> case 2 of Y 2 -> term
--
--   This replacement is what is done using the replaceAt function.
--
--   CompiledClauses also have default branches for when all branches fail (even
--   inner branches), the catchAllBranch. UHC Core does not support this, so
--   we have to add the catchAllBranch to each inner case (here we are calling
--   it omniDefault). To avoid code duplication it is first bound by a let
--   expression.
--
--   Please also note that the clauses of a function don't need to have
--   the same number of arguments.
compileClauses :: QName
                -> Int -- ^ Number of arguments in the definition
                -> Int -- ^ Number of projection arguments.
                -> CC.CompiledClauses -> FreshNameT (CompileT TCM) Fun
compileClauses qnm _ projArgs c = do
  crName <- lift $ getCoreName1 qnm
  e    <- compileClauses' [] Nothing c
  return $ Fun False crName (Just qnm) ("function: " ++ show qnm) [] e
  where
    compileClauses' :: [HsName] -> Maybe Expr -> CC.CompiledClauses -> FreshNameT (CompileT TCM) Expr
    compileClauses' env omniDefault cc = case cc of
        CC.Case n _ | length env <= n -> do
            -- happens if the current subtree expects more arguments
            (args, tf) <- addLambdas ((n - length env) + 1)
            -- the propagated catch all doesn't know that we consumed any arguments,
            -- so just apply it immediately again to the captured args
            let def = (\x -> apps x (map Var args)) <$> omniDefault
            -- now compile the case in the correct env
            tf <$> compileClauses' (env ++ args) def cc
        CC.Case n nc | otherwise -> do
            case CC.catchAllBranch nc of
              Nothing -> let cont = Case (Var (fromMaybe __IMPOSSIBLE__ $ env !!! n))
                          in compileCase env omniDefault n nc cont
              Just de -> do
                  def <- compileClauses' env omniDefault de
                  bindExpr def $ \ defVar ->
                    let cont = Case (Var (fromMaybe __IMPOSSIBLE__ $ env !!! n))
                     in compileCase env (Just $ Var defVar) n nc cont
        CC.Done ps t -> do
                -- requiring additional lambdas happens if clauses have different number of arguments.
                let nLams = length ps - length env + projArgs
                if nLams >= 0 then do
                    (args, tf) <- addLambdas nLams
                    tf <$> substTerm (env ++ args) t
                else
                    __IMPOSSIBLE__
        CC.Fail     -> return IMPOSSIBLE

    compileCase :: [HsName] -> Maybe Expr -> Int -> CC.Case CC.CompiledClauses
                -> ([Branch] -> Maybe Expr -> CaseType -> Expr) -- ^ continuation
                -> FreshNameT (CompileT TCM) Expr
    compileCase env omniDefault casedvar nc cont = do
        case (M.toList $ CC.litBranches nc, M.toList $ CC.conBranches nc) of
            ([], []) -> do
                -- there are no branches, but there might be a catchAll branch
                -- if not, we return the IMPOSSIBLE error term
                return $ fromMaybe IMPOSSIBLE omniDefault
            (lbs, []) -> do
                -- Lit branch
                (brs, ctys) <- unzip <$> (forM lbs $ \(l, cc) -> do
                   cc' <- compileClauses' (replaceAt casedvar env []) omniDefault cc
                   case l of
                       TL.LitChar _ cha     -> return $ (BrChar cha cc', CTChar)
                       TL.LitString _ str   -> return $ (BrString str cc', CTString)
                       -- TODO: Handle other literals
                       _ -> lift $ uhcError $ "case on literal not supported: " ++ show l
                    )
                return $ cont brs omniDefault (head ctys)
            ([], cbs) -> do
                -- Con branch
                brs <- forM cbs $ \(b, CC.WithArity _ cc) -> do

                    conInfo <- lift $ getConstrInfo b
                    let arity' = xconArity $ aciDataCon conInfo
                    vars <- replicateM arity' freshLocalName
                    cc'  <- compileClauses' (replaceAt casedvar env vars) omniDefault cc
                    return $ BrCon (aciDataCon conInfo) (Just b) vars cc'
                -- get datatype info from first branch
                fstConInfo <- lift $ getConstrInfo $ fst $ head cbs
                return $ cont brs omniDefault (CTCon $ aciDataType fstConInfo)
            _ -> __IMPOSSIBLE__ -- having both constructor and lit branches for the same argument doesn't make sense

    -- creates new lambas and puts the new arguments into the environment
    addLambdas :: Int -> FreshNameT (CompileT TCM) ([HsName], (Expr -> Expr))
    addLambdas n | n == 0 = return ([], id)
    addLambdas n | n > 0 = do
        args <- replicateM n freshLocalName
        let tf = foldl1 (.) (map Lam args)
        return (args, tf)
    addLambdas _ | otherwise = __IMPOSSIBLE__


-- | Translate the actual Agda terms, with an environment of all the bound variables
--   from patternmatching. Agda terms are in de Bruijn so we just check the new
--   names in the position.
substTerm :: [HsName] -> T.Term -> FreshNameT (CompileT TCM) Expr
substTerm env term = case T.ignoreSharing $ T.unSpine term of
    T.Var ind es -> do
      let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      case length env <= ind of
        True  -> __IMPOSSIBLE__
        False -> apps1 (fromMaybe __IMPOSSIBLE__ $ env !!! ind) <$>
                   mapM (substTerm env . unArg) args
    T.Lam _ (Abs _ te) -> do
       name <- freshLocalName
       Lam name <$> substTerm (name : env) te
    T.Lam _ (NoAbs _ te) -> do
       name <- freshLocalName
       Lam name <$> substTerm env te
    T.Lit l -> Lit <$> lift (substLit l)
    T.Level l -> substTerm env =<< (lift . lift) (reallyUnLevelView l)
    T.Def q es -> do
      let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      name <- lift $ getCoreName1 q
      def <- theDef <$> (lift . lift) (getConstInfo q)
      let nr = projectionArgs def
      f <- apps1 name . (replicate nr UNIT ++) <$> mapM (substTerm env . unArg) args
      return  f
    T.Con c args -> do
        con <- lift $ getConstrFun $ conName c
        apps1 con <$> mapM (substTerm env . unArg) args
    T.Shared p -> substTerm env $ derefPtr p
    T.Pi _ _ -> return UNIT
    T.Sort _  -> return UNIT
    T.MetaV _ _ -> return UNIT
    T.DontCare _ -> return UNIT

-- | Translate Agda literals to our AUX definition
substLit :: TL.Literal -> CompileT TCM Lit
substLit lit = case lit of
  TL.LitInt    _ i -> return $ LInt i
  TL.LitString _ s -> return $ LString s
  TL.LitChar   _ c -> return $ LChar c
  TL.LitFloat  _ f -> return $ LFloat f
  _ -> uhcError $ "literal not supported: " ++ show lit

