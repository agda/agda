{-# LANGUAGE CPP #-}

-- | Convert from Agda's internal representation to our auxiliary AST.
module Agda.Compiler.Epic.FromAgda where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Char
import Data.Map(Map)
import qualified Data.Map as M
import Data.Maybe

import Agda.Interaction.Options
import Agda.Syntax.Common
import Agda.Syntax.Internal hiding (Term(..))
import qualified Agda.Syntax.Internal as T
import qualified Agda.Syntax.Literal  as TL
import qualified Agda.TypeChecking.CompiledClause as CC
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Level (reallyUnLevelView)
import qualified Agda.TypeChecking.Substitute as S

import Agda.Compiler.Epic.AuxAST
import Agda.Compiler.Epic.CompileState hiding (conPars)
import Agda.Compiler.Epic.Forcing

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Convert from Agda's internal representation to our auxiliary AST.
fromAgda :: Maybe T.Term -> [(QName, Definition)] -> Compile TCM [Fun]
fromAgda msharp defs = catMaybes <$> mapM (translateDefn msharp) defs

-- | Translate an Agda definition to an Epic function where applicable
translateDefn :: Maybe T.Term -> (QName, Definition) -> Compile TCM (Maybe Fun)
translateDefn msharp (n, defini) =
  let n' = unqname n
      epDef = compiledEpic $ defCompiledRep defini
  in case theDef defini of
    d@(Datatype {}) -> do -- become functions returning unit
        vars <- replicateM (fromIntegral $ dataPars d + dataIxs d) newName
        return . return $ Fun True n' ("datatype: " ++ show n) vars UNIT
    f@(Function{}) -> do
        irrF <- gets irrFilters
        let len   = length . clausePats . head .  funClauses $ f
            toEta = fromIntegral (arity (defType defini)) - len
            ccs   = reverseCCBody $ funCompiled f
        forcing <- lift $ gets (optForcing . stPersistentOptions)
        funComp <- if forcing
                    then removeForced ccs (defType defini)
                    else return ccs
        return <$> (etaExpand toEta =<< compileClauses n len funComp)
    Constructor{} -> do -- become functions returning a constructor with their tag
        arit <- lift $ constructorArity n
        tag   <- getConstrTag n
        -- Sharp has to use the primSharp function from AgdaPrelude.e
        case msharp of
          Just (T.Def sharp []) | sharp == n -> return <$> mkFun n' "primSharp" 3
          _    -> return <$> mkCon n tag arit
    r@(Record{}) -> do
        vars <- replicateM (fromIntegral $ recPars r) newName
        return . return $ Fun True n' ("record: " ++ show n) vars UNIT
    a@(Axiom{}) -> do -- Axioms get their code from COMPILED_EPIC pragmas
        case epDef of
            Nothing -> return . return $ EpicFun n' ("AXIOM_UNDEFINED: " ++ show n)
                $ "() -> Any = lazy(error \"Axiom " ++ show n ++ " used but has no computation\")"
            Just x  -> return . return $ EpicFun n' ("COMPILED_EPIC: " ++ show n) x
    p@(Primitive{}) -> do -- Primitives use primitive functions from AgdaPrelude.e of the same name.
                          -- Hopefully they are defined!
      let ar = fromIntegral $ arity $ defType defini
      return <$> mkFun n' (primName p) ar
  where
    mkFun = mkFunGen apps ("primitive: " ++)
    mkCon q tag ari = do
        let name = unqname q
        mkFunGen (flip Con q) (const $ "constructor: " ++ show q) name tag ari
    mkFunGen :: Monad m
            => (name -> [Expr] -> Expr) -- ^ combinator
            -> (name -> String)         -- ^ make comment
            -> Var                      -- ^ Name of the function
            -> name                     -- ^ Primitive function name
            -> Int                      -- ^ Arity ofthe function
            -> Compile m Fun            -- ^ Result?
    mkFunGen comb sh name primname arit = do
        vars <- replicateM arit newName
        return $ Fun True name (sh primname) vars (comb primname (map Var vars))

    etaExpand :: Int -> Fun -> Compile TCM Fun
    etaExpand num fun = do
        names <- replicateM num newName
        return $ fun
            { funExpr = funExpr fun @@ names
            , funArgs = funArgs fun ++ names
            }

    (@@) :: Expr -> [Var] -> Expr
    e @@ [] = e
    e @@ vs = let ts = map Var vs in case e of
      Var var -> apps var ts
      Lam var expr -> case vs of
          v:vs' -> subst var v expr @@ vs'
          []    -> __IMPOSSIBLE__
      Con tag qName es -> Con tag qName (es ++ ts)
      App var es       -> App var (es ++ ts)
      Case expr bs     -> Case expr (map (flip appBranch vs) bs)
      If ea eb ec      -> If ea (eb @@ vs) (ec @@ vs)
      Let var el e'    -> Let var el (e' @@ vs)
      Lazy e'          -> Lazy (e' @@ vs)
      Lit _lit         -> IMPOSSIBLE -- Right?
      UNIT             -> IMPOSSIBLE
      IMPOSSIBLE       -> IMPOSSIBLE

    appBranch :: Branch -> [Var] -> Branch
    appBranch b vs = b {brExpr = brExpr b @@ vs}

reverseCCBody :: CC.CompiledClauses -> CC.CompiledClauses
reverseCCBody cc = case cc of
    CC.Case n (CC.Branches cbr lbr cabr) -> CC.Case n $ CC.Branches (M.map reverseCCBody cbr)
                                                        (M.map reverseCCBody lbr)
                                                        (fmap  reverseCCBody cabr)
    CC.Done i t -> CC.Done i (S.substs (map (flip T.Var []) (reverse $ take (length i) [0..])) t)
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
               -> CC.CompiledClauses -> Compile TCM Fun
compileClauses name nargs c = do
    let n' = unqname name
    vars <- replicateM nargs newName
    e    <- compileClauses' vars Nothing c
    return $ Fun False n' ("function: " ++ show name) vars e
  where
    compileClauses' :: [Var] -> Maybe Var -> CC.CompiledClauses -> Compile TCM Expr
    compileClauses' env omniDefault cc = case cc of
        CC.Case n nc -> case length env <= n of
           True -> __IMPOSSIBLE__
           False -> case CC.catchAllBranch nc of
            Nothing -> Case (Var (env !! n)) <$> compileCase env omniDefault n nc
            Just de -> do
                var <- newName
                def <- compileClauses' env omniDefault de
                Let var (Lazy def) . Case (Var (env !! n)) <$> compileCase env (Just var) n nc
        CC.Done _ t -> substTerm ({- reverse -} env) t
        CC.Fail     -> return IMPOSSIBLE

    compileCase :: [Var] -> Maybe Var -> Int -> CC.Case CC.CompiledClauses
                -> Compile TCM [Branch]
    compileCase env omniDefault casedvar nc = do
        cb <- if M.null (CC.conBranches nc)
           -- Lit branch
           then forM (M.toList (CC.litBranches nc)) $ \(l, cc) -> do
               cc' <- compileClauses' (replaceAt casedvar env []) omniDefault cc
               case l of
                   TL.LitChar _ cha -> return $ BrInt (ord cha) cc'
                   _ -> __IMPOSSIBLE__ -- TODO: Handle other literals
           -- Con branch
           else forM (M.toList (CC.conBranches nc)) $ \(b, cc) -> do
               par  <- getConPar b
               tag  <- getConstrTag b
               vars <- replicateM par newName
               cc'  <- compileClauses' (replaceAt casedvar env vars) omniDefault cc
               return $ Branch tag b vars cc'

        case omniDefault of
            Nothing -> return cb
            Just cc -> do
              return $ cb ++ [Default (Var cc)]

-- | Translate the actual Agda terms, with an environment of all the bound variables
--   from patternmatching. Agda terms are in de Bruijn so we just check the new
--   names in the position.
substTerm :: [Var] -> T.Term -> Compile TCM Expr
substTerm env term = case term of
    T.Var ind args -> case length env <= fromIntegral ind of
        True  -> __IMPOSSIBLE__
        False -> apps (env !! fromIntegral ind) <$> mapM (substTerm env . unArg) args
    T.Lam _ te -> do
       name <- newName
       Lam name <$> substTerm (name : env) (absBody te)
    T.Lit l -> Lit <$> substLit l
    T.Level l -> substTerm env =<< lift (reallyUnLevelView l)
    T.Def q args -> do
      let name = unqname q
      del <- getDelayed q
      f <- apps name <$> mapM (substTerm env . unArg) args
      return $ case del of
        True  -> Lazy f
        False -> f
    T.Con q args -> do
        let con = unqname q
        apps con <$> mapM (substTerm env . unArg) args
    T.Pi _ _ -> return UNIT
    T.Fun _ _ -> return UNIT
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
