{-# OPTIONS_GHC -Wall #-}
-- | 
module Agda.Compiler.Epic.Irrelevant where

import Control.Applicative
import Control.Monad.Trans

import Agda.Syntax.Common
import qualified Agda.Syntax.Internal as T

import Agda.Compiler.Epic.AuxAST
import Agda.Compiler.Epic.CompileState

irrFilter :: T.Type -> [Bool]
irrFilter (T.El _ term) = case term of
    T.Pi  arg ab  -> isRel arg : irrFilter (T.absBody ab)
    T.Fun arg typ -> isRel arg : irrFilter typ
    _ -> []
  where
    isRel :: Arg T.Type -> Bool
    isRel arg = case argRelevance arg of
      Relevant   -> True
      Irrelevant -> False
      Forced     -> False

transformIrr :: MonadIO m => [Fun] -> Compile m [Fun]
transformIrr fs = mapM irrFun fs

irrFun :: Monad m => Fun -> Compile m Fun
irrFun (Fun inline name comment args expr) =
    Fun inline name comment args <$> irrExpr expr
irrFun e@(EpicFun{}) = return e

irrExpr :: Monad m => Expr -> Compile m Expr
irrExpr expr = case expr of
    Var v        -> return $ Var v
    Lit l        -> return $ Lit l
    Lam v e      -> Lam v <$> irrExpr e
    Con tag q es -> do
        irrFilt <- getIrrFilter q
        return $ Con tag q $ pairwiseFilter irrFilt es
    App v es     -> App v <$> mapM irrExpr es
    Case e bs    -> Case <$> irrExpr e <*> mapM irrBranch bs
    Let v e e'   -> Let v <$> irrExpr e <*> irrExpr e'
    If a b c     -> If <$> irrExpr a <*> irrExpr b <*> irrExpr c
    Lazy e       -> Lazy <$> irrExpr e
    UNIT         -> return expr
    IMPOSSIBLE   -> return expr

irrBranch :: Monad m => Branch -> Compile m Branch
irrBranch br = case br of
    Branch  tag name vars e -> do
        ir <- getIrrFilter name
        let vs = pairwiseFilter ir vars
            subs = pairwiseFilter (map not ir) vars
            e'   = foldr (\x ex -> subst x "primUnit" ex) e subs
        Branch tag name vs <$> irrExpr e'
    BrInt i e -> BrInt i <$> irrExpr e
    Default e -> Default <$> irrExpr e