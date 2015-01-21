{-# LANGUAGE CPP, DoAndIfThenElse #-}

-- | Convert from Agda's internal representation to our auxiliary AST.
--
--
-- The coinduction kit is translated the same way as in MAlonzo:
-- flat = id
-- sharp = id
-- -> There is no runtime representation of Coinductive values.
-- The coinduction kit is always a postulate, so we don't have to
-- worry about clauses trying to pattern match on Infinity-values.
module Agda.Compiler.UHC.FromAgda where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Char
import qualified Data.Map as M
import Data.Maybe
import Data.List
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
import Agda.Syntax.Scope.Base

import Agda.Compiler.UHC.Pragmas.Base
import Agda.Compiler.UHC.AuxAST
import Agda.Compiler.UHC.AuxASTUtil
import Agda.Compiler.UHC.CompileState
import Agda.Compiler.UHC.ModuleInfo
import Agda.Compiler.UHC.Builtins
import Agda.Compiler.UHC.Primitives
import Agda.Compiler.UHC.Core
import Agda.Compiler.UHC.Naming

import UHC.Light.Compiler.Core.API as CA

#include "undefined.h"
import Agda.Utils.Impossible

-- | Convert from Agda's internal representation to our auxiliary AST.
fromAgdaModule :: ModuleName
    -> [AModuleInfo]     -- Module info of imported modules.
    -> [(QName, Definition)]
    -> TCM (AMod, AModuleInfo)
fromAgdaModule modNm modImps defs = do
  kit <- coinductionKit

  btins <- getBuiltins

  reportSLn "uhc" 15 "Building name database..."
  defNames <- collectNames btins defs
  nameMp <- assignCoreNames modNm defNames
  reportSLn "uhc" 25 $ "NameMap for " ++ show modNm ++ ":\n" ++ show nameMp


  (mod', modInfo') <- runCompileT kit btins modNm modImps nameMp (do
    lift $ reportSLn "uhc" 10 "Translate datatypes..."
    -- Translate and add datatype information
    dats <- translateDataTypes defs
    let conMp = buildConMp dats
    addConMap conMp

    lift $ reportSLn "uhc" 25 $ "Constructor Map for " ++ show modNm ++ ":\n" ++ show conMp


    funs <- evalFreshNameT "nl.uu.agda.from-agda" (catMaybes <$> mapM translateDefn defs)

    return $ AMod { xmodName = modNm
                  , xmodFunDefs = funs
                  , xmodDataTys = dats
                  }
    )

  return (mod', modInfo')
  where buildConMp :: [ADataTy] -> M.Map QName AConInfo
        buildConMp dts = M.fromList $ concatMap datToConInfo dts
        datToConInfo :: ADataTy -> [(QName, AConInfo)]
        datToConInfo dt = [(xconQName con, AConInfo dt con) | con <- xdatCons dt]

-- | Collect module-level names.
collectNames :: BuiltinCache -> [(QName, Definition)] -> TCM [AgdaName]
collectNames btins defs = do
{-  scope <- lift getScope
  modScope <- (scopeModules scope M.!) <$> getCurrentModule
  lift $ printScope "TEST" 20 "TEST"

  -- TODO we ignore sub modules here right now. In the future, what should we do here?
  let scope' = exportedNamesInScope modScope-}

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
                isBtin = isBuiltin btins qnm
                isForeign = isJust $ compiledCore $ defCompiledRep def
            -- builtin/foreign constructors already have a core-level representation, so we don't need any fresh names
            -- but for the datatypes themselves we still want to create the type-dummy function
            in if ty == EtConstructor && (isForeign || isBtin) then Nothing
               else Just AgdaName
                { anName = qnm
                , anType = ty
                , anNeedsAgdaExport = True -- TODO, only set this to true for things which are actually exported
                -- TODO we should either remove this or make it work... just disable core export for the time being...
                , anCoreExport = AceNo {-if (isForeign || isBtin) && ty /= EtFunction
                        then AceNo      -- it doesn't make sense to export foreign/builtin datatypes on the core level
                        else AceWanted -- TODO, add pragma to set this to No/Required-}
                , anForceName = Nothing -- TODO add pragma to force name
                }


translateDataTypes :: [(QName, Definition)] -> CompileT TCM [ADataTy]
translateDataTypes defs = do
  btins <- getBuiltinCache
  kit <- getCoinductionKit
  -- first, collect all constructors
  constrMp <- M.unionsWith (++)
    <$> mapM (\(n, def) ->
        case theDef def of
            d@(Constructor {}) -> do
                let foreign = compiledCore $ defCompiledRep def
                arity <- lift $ (fst <$> conArityAndPars n)
                let conFun = ADataCon n
                con <- case (n `M.lookup` (btccCtors btins), foreign) of
                    (Just (_, ctag), Nothing) -> return $ Right (conFun ctag)
                    (Nothing, Just (CrConstr crcon)) -> return $ Right (conFun $ coreConstrToCTag crcon arity)
                    (Nothing, Nothing)   -> do
                        conCrNm <- getCoreName1 n
                        return $ Left (\tyCrNm tag -> conFun (mkCTag tyCrNm conCrNm tag arity))
                    _ -> __IMPOSSIBLE__ -- being builtin and foreign at the same time makes no sense
                return $ M.singleton (conData d) [con]
            _ -> return M.empty
        ) defs

  let handleDataRecDef = (\n def -> do
            let foreign = compiledCore $ defCompiledRep def
            let cons = M.findWithDefault [] n constrMp
            case (n `M.lookup` (btccTys btins), foreign, partitionEithers cons) of
              (Just (btin, tyNm), Nothing, ([], cons')) -> do -- builtins
                    return $ Just (ADataTy tyNm n cons' (ADataImplBuiltin btin))
              (Nothing, Just (CrType crty), ([], cons')) -> do -- foreign datatypes (COMPILED_CORE_DATA)
                    let (tyNm, impl) = case crty of
                                CTMagic tyNm nm -> (tyNm, ADataImplMagic nm)
                                CTNormal tyNm -> (tyNm, ADataImplForeign)
                    return $ Just (ADataTy tyNm n cons' impl)
              (Nothing, Nothing, (cons', [])) -> do
                    tyCrNm <- getCoreName1 n
                    -- build ctags, assign tag numbers
                    let cons'' = map (\((conFun), i) -> conFun tyCrNm i) (zip cons' [0..])
                    return $ Just (ADataTy (Just tyCrNm) n cons'' ADataImplNormal)
              _ -> __IMPOSSIBLE__ -- datatype is builtin <=> all constructors have to be builtin
              )

  catMaybes <$> mapM
    (\(n, def) -> case theDef def of
        (Record{}) -> handleDataRecDef n def
        -- coinduction kit gets erased in the translation to AuxAST
        (Datatype {}) | Just n /= (nameOfInf <$> kit)
                -> handleDataRecDef n def
        _       -> return Nothing
    ) defs


-- | Translate an Agda definition to an Epic function where applicable
translateDefn :: (QName, Definition) -> FreshNameT (CompileT TCM) (Maybe Fun)
translateDefn (n, defini) = do
  crName <- lift $ getCoreName n
  let crRep = compiledCore $ defCompiledRep defini
  kit <- lift getCoinductionKit
  case theDef defini of
    d@(Datatype {}) -> do -- become functions returning unit
        vars <- replicateM (dataPars d + dataIxs d) freshLocalName
        return . return $ Fun True (fromMaybe __IMPOSSIBLE__ crName) (Just n) ("datatype: " ++ show n) vars UNIT
    f@(Function{}) | Just n == (nameOfFlat <$> kit) -> do
        -- ignore the two type arguments
        Just <$> mkIdentityFun n "coind-sharp" 2
    f@(Function{}) | otherwise -> do
        let projArgs = projectionArgs f
            cc       = fromMaybe __IMPOSSIBLE__ $ funCompiled f
        -- let projArgs = maybe 0 (pred . projIndex) (funProjection f)
        let ccs = reverseCCBody projArgs cc
        let len   = (+ projArgs) . length . clausePats . head .  funClauses $ f
            ty    = (defType defini)
        -- forcing <- lift $ gets (optForcing . stPersistentOptions)
        lift . lift $ reportSDoc "uhc.fromagda" 5 $ text "compiling fun:" <+> prettyTCM n
        lift . lift $ reportSDoc "uhc.fromagda" 5 $ text "len:" <+> (text . show) len
        lift . lift $ reportSDoc "uhc.fromagda" 15 $ text "pats:" <+> (text . show) (clausePats
                    $ head $ funClauses f)
        lift . lift $ reportSDoc "uhc.fromagda" 15 $ text "type:" <+> (text . show) ty

        lift . lift $ reportSDoc "uhc.fromagda" 15 $ text "ccs: " <+> (text . show) ccs
        res <- return <$> compileClauses n len ccs
{-        pres <- case res of
          Nothing -> return Nothing
          Just  c -> return <$> prettyEpicFun c
        lift $ reportSDoc "" 5 $ text $ show pres -- (fmap prettyEpicFun res)-}
        return res
    Constructor{} | Just n == (nameOfSharp <$> kit) -> do
        Just <$> mkIdentityFun n "coind-sharp" 0
    Constructor{} | otherwise -> do -- become functions returning a constructor with their tag

        case crName of
          (Just crNm) -> do
                conInfo <- lift $ getConstrInfo n
                let conCon = aciDataCon conInfo
                    arity = xconArity conCon

                vars <- replicateM arity freshLocalName
                return $ Just $ Fun True (ctagCtorName $ xconCTag conCon) (Just n)
                        ("constructor: " ++ show n) vars (Con (aciDataType conInfo) conCon (map Var vars))
          Nothing -> return Nothing -- either foreign or builtin type. We can just assume existence of the wrapper functions then.

        -- Sharp has to use the primSharp function from AgdaPrelude.e
{-        case msharp of
          Just (T.Def sharp []) | sharp == n -> return <$> mkFun n n' "primSharp" 3
          _    -> return <$> mkCon n tag arit-}
    r@(Record{}) -> do
        vars <- replicateM (recPars r) freshLocalName
        return . return $ Fun True (fromMaybe __IMPOSSIBLE__ crName) (Just n) ("record: " ++ show n) vars UNIT
    a@(Axiom{}) -> do -- Axioms get their code from COMPILED_CORE pragmas
        case crRep of
            -- TODO generate proper core errors
            Nothing -> return . return $ CoreFun (fromMaybe __IMPOSSIBLE__ crName) (Just n) ("AXIOM_UNDEFINED: " ++ show n)
                (coreImpossible $ "Axiom " ++ show n ++ " used but has no computation.") 0 -- TODO can we set arity to 0 here? not sure if we can..., maybe pass around arity info for Axiom?
            Just (CrDefn x)  -> return . return $ CoreFun (fromMaybe __IMPOSSIBLE__ crName) (Just n) ("COMPILED_CORE: " ++ show n) x 2 -- TODO HACK JUST FOR TESTIN
            _       -> error "Compiled core must be def, something went wrong."
    p@(Primitive{}) -> do -- Primitives use primitive functions from UHC.Agda.Builtins of the same name.

      let ar = arity $ defType defini
      case primName p `M.lookup` primFunctions of
        Nothing     -> error $ "Primitive " ++ show (primName p) ++ " declared, but no such primitive exists."
        (Just expr) -> do
                expr' <- lift expr
                return $ Just $ CoreFun (fromMaybe __IMPOSSIBLE__ crName) (Just n) ("primitive: " ++ primName p) expr' ar --mkFunGen n (const $ App anm) ("primitive: " ++) (fromMaybe __IMPOSSIBLE__ crName) (primName p) ar
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
    modOf = reverse . dropWhile (/='.') . reverse
    mkFunGen :: QName                    -- ^ Original name
            -> (name -> [Expr] -> Expr) -- ^ combinator
            -> (name -> String)         -- ^ make comment
            -> HsName                      -- ^ Name of the function
            -> name                     -- ^ Primitive function name
            -> Int                      -- ^ Arity ofthe function
            -> FreshNameT (CompileT TCM) Fun            -- ^ Result?
    mkFunGen qn comb sh name primname arit = do
        vars <- replicateM arit freshLocalName
        return $ Fun True name (Just qn) (sh primname) vars (comb primname (map Var vars))

{-    (@@) :: Expr -> [AName] -> Expr
    e @@ [] = e
    e @@ vs = let ts = map Var vs in case e of
      Var var -> apps var ts
      Lam var expr -> case vs of
          v:vs' -> subst var v expr @@ vs'
          []    -> __IMPOSSIBLE__
      Con tag qName es -> Con tag qName (es ++ ts)
      App var es       -> App var (es ++ ts)
      Case expr bs     -> Case expr (map (flip appBranch vs) bs)
      Let var el e'    -> lett var el (e' @@ vs)
      Lit _lit         -> IMPOSSIBLE -- Right?
      UNIT             -> IMPOSSIBLE
      IMPOSSIBLE       -> IMPOSSIBLE

    appBranch :: Branch -> [AName] -> Branch
    appBranch b vs = b {brExpr = brExpr b @@ vs}-}


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
--   inner branches), the catchAllBranch. Epic does not support this, so
--   we have to add the catchAllBranch to each inner case (here we are calling
--   it omniDefault). To avoid code duplication it is first bound by a let
--   expression.
compileClauses :: QName
                -> Int -- ^ Number of arguments in the definition
                -> CC.CompiledClauses -> FreshNameT (CompileT TCM) Fun
compileClauses qnm nargs c = do
  crName <- lift $ getCoreName1 qnm
  vars <- replicateM nargs freshLocalName
  e    <- compileClauses' vars Nothing c
  return $ Fun False crName (Just qnm) ("function: " ++ show qnm) vars e
  where
    compileClauses' :: [HsName] -> Maybe Expr -> CC.CompiledClauses -> FreshNameT (CompileT TCM) Expr
    compileClauses' env omniDefault cc = case cc of
        CC.Case n nc -> case length env <= n of
           True -> __IMPOSSIBLE__
           False -> case CC.catchAllBranch nc of
            Nothing -> let cont = Case (Var (fromMaybe __IMPOSSIBLE__ $ env !!! n))
                        in compileCase env omniDefault n nc cont
            Just de -> do
                def <- compileClauses' env omniDefault de
                bindExpr def $ \ var ->
                  let cont = Case (Var (fromMaybe __IMPOSSIBLE__ $ env !!! n))
                   in compileCase env (Just $ Var var) n nc cont
        CC.Done _ t -> substTerm ({- reverse -} env) t
        CC.Fail     -> return IMPOSSIBLE

    compileCase :: [HsName] -> Maybe Expr -> Int -> CC.Case CC.CompiledClauses
                -> ([Branch] -> Maybe Expr -> CaseType -> a) -- ^ continuation
                -> FreshNameT (CompileT TCM) a
    compileCase env omniDefault casedvar nc cont = do
        (cb, cty) <- case (M.toList $ CC.litBranches nc, M.toList $ CC.conBranches nc) of
            ([], []) -> __IMPOSSIBLE__ -- can this actually happen? just fail for now.
            (lbs, []) -> do
                -- Lit branch
                brs <- forM lbs $ \(l, cc) -> do
                   cc' <- compileClauses' (replaceAt casedvar env []) omniDefault cc
                   case l of
                       TL.LitChar _ cha -> return $ BrChar cha cc'
                       -- TODO: Handle other literals
                       _ -> lift $ uhcError $ "case on literal not supported: " ++ show l
                return (brs, CTChar)
            ([], cbs) -> do
                -- Con branch
                brs <- forM cbs $ \(b, CC.WithArity ar cc) -> do

                    conInfo <- lift $ getConstrInfo b
                    let arity = xconArity $ aciDataCon conInfo
                    vars <- replicateM arity freshLocalName
                    cc'  <- compileClauses' (replaceAt casedvar env vars) omniDefault cc
                    return $ BrCon (aciDataCon conInfo) (Just b) vars cc'
                -- get datatype info from first branch
                fstConInfo <- lift $ getConstrInfo $ fst $ head cbs
                return (brs, CTCon $ aciDataType fstConInfo)
            _ -> __IMPOSSIBLE__ -- having both constructor and lit branches for the same argument doesn't make sense

        return $ cont cb omniDefault cty

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
       -- the MAlonzo backend counts NoAbs variables towards the de-bruijn indexes,
       -- let's just do that here as well. But is this correct?
       Lam name <$> substTerm (__IMPOSSIBLE__ : env) te
    T.Lit l -> Lit <$> lift (substLit l)
    T.Level l -> substTerm env =<< (lift . lift) (reallyUnLevelView l)
    T.Def q es -> do
      let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      name <- lift $ getCoreName1 q
--      del <- getDelayed q
      def <- theDef <$> (lift . lift) (getConstInfo q)
      let nr = projectionArgs def
{- MOVED to Signature.hs
             case def of
                Function{funProjection = Just p} -> pred $ projIndex p
                _ -> 0
 -}
      f <- apps1 name . (replicate nr UNIT ++) <$> mapM (substTerm env . unArg) args
      -- TODO PH can we do that here?
      return  f
        {-$ case del of
        True  -> Lazy f
        False -> f-}
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

