{-# LANGUAGE CPP #-}

-- | Convert from Agda's internal representation to our auxiliary AST.
module Agda.Compiler.UHC.FromAgda where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Char
import qualified Data.Map as M
import Data.Maybe

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

import Agda.Compiler.UHC.CoreSyntax (CoreConstr)
import Agda.Compiler.UHC.AuxAST
import Agda.Compiler.UHC.CompileState
import Agda.Compiler.UHC.Interface
import Agda.Compiler.UHC.Primitives
import Agda.Compiler.UHC.Core

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Convert from Agda's internal representation to our auxiliary AST.
fromAgdaModule :: Maybe T.Term -> String -> [(QName, Definition)] -> Compile TCM AMod
fromAgdaModule msharp modNm defs = do
  btins <- lift getBuiltins
  funs <- catMaybes <$> mapM (translateDefn btins msharp) defs
  dats <- translateDataTypes btins

  return $ AMod { xmodName = modNm
                , xmodFunDefs = funs
                , xmodDataTys = dats
                }

-- | Translate the datatypes to the aux ast. The data types are already stored
--   in the compile monad.
translateDataTypes :: BuiltinCache -> Compile TCM [ADataTy]
translateDataTypes btins = do
    constrs <- getsEI constrTags
    dataCons <- mapM f (M.toList constrs)
    let dataCons' = filter (\(x,_) -> not $ x `M.member` btccTys btins) $ M.toList $ M.unionsWith (++) dataCons
    
    return $ map (\(tyNm, dConL) -> ADataTy (unqname tyNm) tyNm dConL) dataCons'
    where f :: (QName, Tag) -> Compile TCM (M.Map QName [ADataCon])
          f (qn, t) = do
              cr <- (lift $ getConstInfo qn) >>= return . compiledCore . defCompiledRep
              case cr of
                (Just _) -> return M.empty
                Nothing  -> do
                  a <- getConArity qn
                  -- TODO do we have to put full qn into con name?
                  return $ M.singleton (qnameTypeName qn) [ADataCon
                        { xconArity = a
                        , xconLocalName = qnameCtorName qn
                        , xconQName = qn
                        , xconTag = t
                        }]
          qnameTypeName :: QName -> QName
          qnameTypeName = qnameFromList . init . qnameToList

          qnameCtorName :: QName -> String
          qnameCtorName = show . last . qnameToList



-- | Translate an Agda definition to an Epic function where applicable
translateDefn :: BuiltinCache -> Maybe T.Term -> (QName, Definition) -> Compile TCM (Maybe Fun)
translateDefn btins msharp (n, defini) =
  let n' = unqname n
      crRep = compiledCore $ defCompiledRep defini
  in case theDef defini of
    d@(Datatype {}) -> do -- become functions returning unit
        vars <- replicateM (dataPars d + dataIxs d) newName
        return . return $ Fun True n' (Just n) ("datatype: " ++ show n) vars UNIT
    f@(Function{}) -> do
        let projArgs = projectionArgs f
            cc       = fromMaybe __IMPOSSIBLE__ $ funCompiled f
        -- let projArgs = maybe 0 (pred . projIndex) (funProjection f)
        let ccs = reverseCCBody projArgs cc
        let len   = (+ projArgs) . length . clausePats . head .  funClauses $ f
            ty    = (defType defini)
        -- forcing <- lift $ gets (optForcing . stPersistentOptions)
        lift $ reportSDoc "uhc.fromagda" 5 $ text "compiling fun:" <+> prettyTCM n
        lift $ reportSDoc "uhc.fromagda" 5 $ text "len:" <+> (text . show) len
        lift $ reportSDoc "uhc.fromagda" 5 $ text "pats:" <+> (text . show) (clausePats
                    $ head $ funClauses f)
        lift $ reportSDoc "uhc.fromagda" 5 $ text "type:" <+> (text . show) ty
        modify $ \s -> s {curFun = show n}
        lift $ reportSDoc "uhc.fromagda" 5 $ text "ccs: " <+> (text . show) ccs
        res <- return <$> compileClauses btins n len ccs
{-        pres <- case res of
          Nothing -> return Nothing
          Just  c -> return <$> prettyEpicFun c
        lift $ reportSDoc "" 5 $ text $ show pres -- (fmap prettyEpicFun res)-}
        return res
    Constructor{} -> do -- become functions returning a constructor with their tag
        arit <- lift $ constructorArity n
        tag   <- getConstrTag n
        case (crRep, n `M.lookup` (btccCtors btins)) of
          (Just (CrConstr (dt, ctr, tg)), Nothing) -> mkCrCtorFun n (ConNamed dt ctr tg) arit
          (Just _, Just _)       -> error $ "Compiled core must not be specified for builtin " ++ show n
          (Just _, Nothing)      -> error "Compiled core must be def, something went wrong."
          (Nothing, Just btcon) -> mkCrCtorFun n btcon arit
          (Nothing, Nothing)     -> return <$> mkCon n tag arit
        -- Sharp has to use the primSharp function from AgdaPrelude.e
{-        case msharp of
          Just (T.Def sharp []) | sharp == n -> return <$> mkFun n n' "primSharp" 3
          _    -> return <$> mkCon n tag arit-}
    r@(Record{}) -> do
        vars <- replicateM (recPars r) newName
        return . return $ Fun True n' (Just n) ("record: " ++ show n) vars UNIT
    a@(Axiom{}) -> do -- Axioms get their code from COMPILED_CORE pragmas
        case crRep of
            -- TODO generate proper core errors
            Nothing -> return . return $ CoreFun n' (Just n) ("AXIOM_UNDEFINED: " ++ show n)
                $ coreError ("Axiom " ++ show n ++ " used but has no computation.")
            Just (CrDefn x)  -> return . return $ CoreFun n' (Just n) ("COMPILED_CORE: " ++ show n) x
            _       -> error "Compiled core must be def, something went wrong."
    p@(Primitive{}) -> do -- Primitives use primitive functions from UHC.Agda.Builtins of the same name.
      
      let ar = arity $ defType defini
      case primName p `M.lookup` primFunctions of
        Nothing     -> error $ "Primitive " ++ show (primName p) ++ " declared, but no such primitive exists."
        (Just anm)  -> return <$> mkFunGen n (const $ App anm) ("primitive: " ++) (unqname n) (primName p) ar
  where
    modOf = reverse . dropWhile (/='.') . reverse
    mkCrCtorFun n (ConNamed dt ctr _) arit = do
        -- UHC generates a wrapper function for all datatypes, so just call that one
        let ctorFun = (modOf dt) ++ ctr
        return <$> mkFunGen n (const $ App $ ANmCore ctorFun) (const $ "constructor: " ++ show n) (unqname n) ctr arit
    mkCrCtorFun n (ConUnit) 0 = return $ return $ Fun True (unqname n) (Just n) "Unit constructor function" [] UNIT
    mkCrCtorFun _ _ _ = __IMPOSSIBLE__
    mkCon q tag ari = do
        let name = unqname q
        mkFunGen q (flip Con q) (const $ "constructor: " ++ show q) name tag ari
    mkFunGen :: QName                    -- ^ Original name
            -> (name -> [Expr] -> Expr) -- ^ combinator
            -> (name -> String)         -- ^ make comment
            -> AName                      -- ^ Name of the function
            -> name                     -- ^ Primitive function name
            -> Int                      -- ^ Arity ofthe function
            -> Compile TCM Fun            -- ^ Result?
    mkFunGen qn comb sh name primname arit = do
        vars <- replicateM arit newName
        return $ Fun True name (Just qn) (sh primname) vars (comb primname (map Var vars))

    (@@) :: Expr -> [AName] -> Expr
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
    appBranch b vs = b {brExpr = brExpr b @@ vs}

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
compileClauses :: BuiltinCache -> QName
               -> Int -- ^ Number of arguments in the definition
               -> CC.CompiledClauses -> Compile TCM Fun
compileClauses btins name nargs c = do
    let n' = unqname name
    vars <- replicateM nargs newName
    e    <- compileClauses' vars Nothing c
    return $ Fun False n' (Just name) ("function: " ++ show name) vars e
  where
    compileClauses' :: [AName] -> Maybe AName -> CC.CompiledClauses -> Compile TCM Expr
    compileClauses' env omniDefault cc = case cc of
        CC.Case n nc -> case length env <= n of
           True -> __IMPOSSIBLE__
           False -> case CC.catchAllBranch nc of
            Nothing -> Case (Var (fromMaybe __IMPOSSIBLE__ $ env !!! n)) <$>
                         compileCase btins env omniDefault n nc
            Just de -> do
                def <- compileClauses' env omniDefault de
                bindExpr def $ \ var ->
                  Case (Var (fromMaybe __IMPOSSIBLE__ $ env !!! n)) <$>
                    compileCase btins env (Just var) n nc
        CC.Done _ t -> substTerm ({- reverse -} env) t
        CC.Fail     -> return IMPOSSIBLE

    compileCase :: BuiltinCache -> [AName] -> Maybe AName -> Int -> CC.Case CC.CompiledClauses
                -> Compile TCM [Branch]
    compileCase btins env omniDefault casedvar nc = do
        cb <- if M.null (CC.conBranches nc)
           -- Lit branch
           then forM (M.toList (CC.litBranches nc)) $ \(l, cc) -> do
               cc' <- compileClauses' (replaceAt casedvar env []) omniDefault cc
               case l of
                   -- TODO: Handle other literals
                   _ -> epicError $ "case on literal not supported: " ++ show l
           -- Con branch
           else forM (M.toList (CC.conBranches nc)) $ \(b, CC.WithArity ar cc) -> do
               def <- lift $ getConstInfo b
               let crr = defCoreDef def
               arit  <- getConArity b -- Andreas, 2012-10-12: is the constructor arity @ar@ from Agda the same as the one from the Epic backen?
               vars <- replicateM arit newName
               cc'  <- compileClauses' (replaceAt casedvar env vars) omniDefault cc
               case (b `M.lookup` (btccCtors btins), crr, theDef def) of
                   (Just btCon, Nothing, Constructor{}) -> do
                       return $ CoreBranch (builtinConSpecToCoreConstr btCon) vars cc'
                   (Nothing, Just (CrConstr crCon), Constructor{}) -> do
                       return $ CoreBranch crCon vars cc'
                   (Nothing, Nothing, _) -> do
                       tag <- getConstrTag b
                       return $ Branch tag b vars cc'
                   _ -> __IMPOSSIBLE__


-- always use the original name for a constructor even when it's redefined.
-- conhqn :: QName -> TCM HS.QName
-- conhqn q = do
--     cq  <- canonicalName q
--         def <- getConstInfo cq
--             hsr <- compiledHaskell . defCompiledRep <$> getConstInfo cq
--                 case (compiledHaskell (defCompiledRep def), theDef def) of
--                       (Just (HsDefn _ hs), Constructor{}) -> return $ HS.UnQual $ HS.Ident hs
--                             _                                   -> xhqn "C" cq
--

        case omniDefault of
            Nothing -> return cb
            Just cc -> do
              return $ cb ++ [Default (Var cc)]

-- | Translate the actual Agda terms, with an environment of all the bound variables
--   from patternmatching. Agda terms are in de Bruijn so we just check the new
--   names in the position.
substTerm :: [AName] -> T.Term -> Compile TCM Expr
substTerm env term = case T.unSpine term of
    T.Var ind es -> do
      let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      case length env <= ind of
        True  -> __IMPOSSIBLE__
        False -> apps (fromMaybe __IMPOSSIBLE__ $ env !!! ind) <$>
                   mapM (substTerm env . unArg) args
    T.Lam _ (Abs _ te) -> do
       name <- newName
       Lam name <$> substTerm (name : env) te
    T.Lam _ (NoAbs _ te) -> do
       name <- newName
       Lam name <$> substTerm env te
    T.ExtLam _ _ -> __IMPOSSIBLE__
    T.Lit l -> Lit <$> substLit l
    T.Level l -> substTerm env =<< lift (reallyUnLevelView l)
    T.Def q es -> do
      let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      let name = unqname q
      del <- getDelayed q
      def <- theDef <$> lift (getConstInfo q)
      let nr = projectionArgs def
{- MOVED to Signature.hs
             case def of
                Function{funProjection = Just p} -> pred $ projIndex p
                _ -> 0
 -}
      f <- apps name . (replicate nr UNIT ++) <$> mapM (substTerm env . unArg) args
      -- TODO PH can we do that here?
      return  f {-$ case del of
        True  -> Lazy f
        False -> f-}
    T.Con c args -> do
        let con = unqname $ conName c
        apps con <$> mapM (substTerm env . unArg) args
    T.Shared p -> substTerm env $ derefPtr p
    T.Pi _ _ -> return UNIT
    T.Sort _  -> return UNIT
    T.MetaV _ _ -> return UNIT
    T.DontCare _ -> return UNIT

-- | Translate Agda literals to our AUX definition
substLit :: TL.Literal -> Compile TCM Lit
substLit lit = case lit of
  TL.LitInt    _ i -> return $ LInt i
  TL.LitString _ s -> return $ LString s
  TL.LitChar   _ c -> return $ LChar c
  TL.LitFloat  _ f -> return $ LFloat f
  _ -> epicError $ "literal not supported: " ++ show lit

