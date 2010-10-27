
module Eval where

import Control.Applicative
import Term
import Name
import Monad

subst t [] = return t
subst (Closure t sub) env = Closure t . (++env) <$> substEnv sub env
subst t env               = return $ Closure t env

substEnv sub env = mapM s sub
  where
    s (x, v) = (,) x <$> subst v env

apply (Var x vs)      v = return $ Var x (vs ++ [v])
apply (Con c vs)      v = return $ Con c (vs ++ [v])
apply (Lam x t)       v = subst t [(x, v)]
apply (Closure t env) v = flip subst env =<< apply t v

apply' u [] = return u
apply' u (v:vs) = do
  uv <- apply u v
  apply' uv vs

reduce :: Term -> TC Term
reduce (Var x vs) = do
  vx <- varValue x
  case vx of
    Var x' [] | x == x' -> apply' vx =<< mapM reduce vs
    _                   -> reduce =<< apply' vx vs
reduce (Con c vs) = do
  vc <- conValue c
  case vc of
    Con c' [] | c == c' -> apply' vc =<< mapM reduce vs
    _                   -> reduce =<< apply' vc vs
reduce (Lam x t) = do
  env <- getSubst
  subst (Lam x t) env
reduce (Closure v env) = do
  env' <- getSubst
  sub <- substEnv env env'
  withSubst sub $ reduce v

normalize v = do
  v <- reduce v
  case v of
    Closure (Lam x t) env ->
      withSubst ((x, Var x []) : env) $
        Lam x <$> normalize t
    _ -> return v
