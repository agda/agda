
module Check where

import Control.Applicative

import qualified Syntax.Abs as A
import Name
import Term
import Monad
import Eval

checkProg :: A.Program -> TC [Decl]
checkProg (A.Prog ds) = mapM checkDecl ds

checkDecl :: A.Decl -> TC Decl
checkDecl (A.Def (A.Ident x) e) = do
  v <- checkExpr e
  x <- addDef x v
  return $ Def x v
checkDecl (A.Const (A.Ident x)) = do
  x <- addConst x
  return $ Decl x

checkExpr :: A.Expr -> TC Term
checkExpr (A.Var (A.Ident x)) = resolveName x
checkExpr (A.App s t) = do
  u <- checkExpr s
  v <- checkExpr t
  apply u v
checkExpr (A.Lam (A.Ident x) t) =
  bindVar x $ \x -> do
  v <- checkExpr t
  return $ Lam x v
