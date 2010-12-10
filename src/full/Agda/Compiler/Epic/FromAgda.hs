{-# OPTIONS_GHC -Wall #-}
-- | Convert from Agda's internal representation to our auxiliary AST.
module Agda.Compiler.Epic.FromAgda where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Data.Char
import Data.Map(Map)
import qualified Data.Map as M
import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Internal hiding (Term(..))
import qualified Agda.Syntax.Internal as T
import qualified Agda.Syntax.Literal  as TL
import qualified Agda.TypeChecking.CompiledClause as CC
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce

import Agda.Compiler.Epic.AuxAST
import Agda.Compiler.Epic.CompileState hiding (conPars)

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Convert from Agda's internal representation to our auxiliary AST.
fromAgda :: MonadTCM m => Maybe T.Term -> [(QName, Definition)] -> Compile m [Fun]
fromAgda msharp defs = catMaybes <$> mapM (translateDefn msharp) defs

-- | Translate an Agda definition to an Epic function where applicable
translateDefn :: MonadTCM m => (Maybe T.Term) -> (QName, Definition) -> Compile m (Maybe Fun)
translateDefn msharp (n, defini) = let n' = unqname n in case theDef defini of
    d@(Datatype {}) -> do -- become functions returning unit
        vars <- replicateM (fromIntegral $ dataPars d + dataIxs d) newName
        return . return $ Fun True n' ("datatype: " ++ show n) vars UNIT
    f@(Function{}) -> do
        let len = length . clausePats . translatedClause . head .  funClauses $ f
        return <$> compileClauses n len (funCompiled f)
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
        case axEpDef a of
            Nothing -> return Nothing -- TODO: generate a good error message
            Just x  -> return . return $ EpicFun n' ("COMPILED_EPIC: " ++ show n) x
    p@(Primitive{}) -> do -- Prifailmitives use primitive functions from AgdaPrelude.e of the same name.
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
compileClauses :: MonadTCM m
               => QName
               -> Int -- ^ Number of arguments in the definition
               -> CC.CompiledClauses -> Compile m Fun
compileClauses name nargs c = do
    let n' = unqname name
    vars <- replicateM nargs newName
    e    <- compileClauses' vars Nothing c
    return $ Fun False n' ("function: " ++ show name) vars e
  where
    compileClauses' :: MonadTCM m => [Var] -> Maybe Var -> CC.CompiledClauses -> Compile m Expr
    compileClauses' env omniDefault cc = case cc of
        CC.Case n nc -> case length env <= n of
           True -> __IMPOSSIBLE__
           False -> case CC.catchAllBranch nc of
            Nothing -> Case (Var (env !! n)) <$> compileCase env omniDefault n nc
            Just de -> do
                var <- newName
                def <- compileClauses' env omniDefault de
                Let var (Lazy def) . Case (Var (env !! n)) <$> compileCase env (Just var) n nc
        CC.Done _ t -> substTerm (reverse env) t
        CC.Fail     -> return IMPOSSIBLE

    compileCase :: MonadTCM m
                => [Var]
                -> Maybe Var
                -> Int
                -> CC.Case CC.CompiledClauses
                -> Compile m [Branch]
    compileCase env omniDefault casedvar nc = do
        cb <- dispatchBranches env omniDefault casedvar nc
        case omniDefault of
            Nothing -> return cb
            Just cc -> do
              return $ cb ++ [Default (Var cc)]

    dispatchBranches :: MonadTCM m
                     => [Var]
                     -> Maybe Var
                     -> Int
                     -> CC.Case CC.CompiledClauses
                     -> Compile m [Branch]
    dispatchBranches env omniDefault casedvar nc = do
        if M.null (CC.conBranches nc)
           then compileLitBranch env omniDefault casedvar (CC.litBranches nc)
           else compileConBranch env omniDefault casedvar (CC.conBranches nc)

    compileConBranch :: MonadTCM m
                     => [Var]
                     -> Maybe Var
                     -> Int
                     -> Map QName CC.CompiledClauses
                     -> Compile m [Branch]
    compileConBranch env omniDefault casedvar bs = forM (M.toList bs) $ \(b, cc) -> do
        par <- getConPar b
        tag <- getConstrTag b
        vars <- replicateM par newName
        cc' <- compileClauses' (replaceAt casedvar env vars) omniDefault cc
        return $ Branch tag b vars cc'

    compileLitBranch :: MonadTCM m
                     => [Var]
                     -> Maybe Var
                     -> Int
                     -> Map TL.Literal CC.CompiledClauses
                     -> Compile m [Branch]
    compileLitBranch env omniDefault _casedvar bs = forM (M.toList bs) $ \(l, cc) -> do
        cc' <- compileClauses' env omniDefault cc
        case l of
            TL.LitChar _ cha -> return $ BrInt (ord cha) cc'
            _ -> __IMPOSSIBLE__ -- TODO: Handle other literals

    replaceAt :: Int -- ^ replace at
              -> [a] -- ^ to replace
              -> [a] -- ^ replace with
              -> [a] -- ^ result?
    replaceAt n xs inserts = let (as, _:bs) = splitAt n xs in as ++ inserts ++ bs

-- | Translate the actual Agda terms, with an environment of all the bound variables
--   from patternmatching. Agda terms are in de Bruijn so we just check the new
--   names in the position.
substTerm :: MonadTCM m => [Var] -> T.Term -> Compile m Expr
substTerm env term = case term of
    T.Var ind args -> case length env <= fromIntegral ind of
        True  -> __IMPOSSIBLE__
        False -> apps (env !! fromIntegral ind) <$> mapM (substTerm env . unArg) args
    T.Lam _ te -> do
       name <- newName
       Lam name <$> substTerm (name : env) (absBody te)
    T.Lit l -> Lit <$> substLit l
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
    T.DontCare  -> return UNIT

-- | Translate Agda literals to our AUX definition
substLit :: Monad m => TL.Literal -> Compile m Lit
substLit lit = case lit of
  TL.LitInt    _ i -> return $ LInt i
  TL.LitLevel  _ i -> return $ LInt i
  TL.LitString _ s -> return $ LString s
  TL.LitChar   _ c -> return $ LChar c
  _ -> fail $ "literal not supported: " ++ show lit

-- | Copy pasted from MAlonzo, HAHA!!!
--   Move somewhere else!
constructorArity :: (MonadTCM tcm, Num a) => QName -> tcm a
constructorArity q = do
  def <- getConstInfo q
  a <- normalise $ defType def
  case theDef def of
    Constructor{ conPars = np } -> return . fromIntegral $ arity a - np
    _ -> fail $ "constructorArity: non constructor: " ++ show q
