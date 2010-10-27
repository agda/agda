module Exp1 where

import Val
import Core.Abs

-- we use de Bruijn indexes

{-
data Exp =
      ELam Name Exp
    | EApp Name [Exp]

    | ESet
    | EFun Name Exp Exp

    | Efun [(Name,Exp)]       -- body of a definition
-}

type Env = [(Ident,Val)]

update :: Env -> Ident -> Val -> Env
update env s u = (s,u):env

getRef s ((s1,u):rest) = if s == s1 then u else getRef s rest
getRef s [] = error ("getRef " ++ show s)  -- this should never occur after scope analysis

eval :: Env -> Exp -> Val
eval env (ELam s e)= Lam (\ u -> eval (update env s u) e)
eval env (EApp n us) = apps (getRef n env) (map (eval env) us)
eval env (EIdent n) = getRef n env
eval env ESet = Set
eval env (EFun s a1 a2) =
 Fun (eval env a1) (\ u -> eval (update env s u) a2)
eval env e = error ("eval " ++ show e)

get s [] = error ("get " ++ show s)     -- should never occur
get s ((s1,u):us) = if s == s1 then u else get s us

evalBody :: Env -> Val -> Exp -> Val   -- v is the type of the recursive expression

evalBody env v (ELam s e) = Lam (\ u -> evalBody (update env s u) (app v u) e)
evalBody env v (Efun nes) =
 Lam f
  where
        f (App (Prim c _) us) = apps (get (Ident c) nvs) us
        f w = app v w
        nvs = map (\ (Bcon c e) -> (c,eval env e)) nes
evalBody env v e = eval env e
