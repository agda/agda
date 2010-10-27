module Exp where

import Val

-- we use de Bruijn indexes

data Exp =
      ELam Exp
    | EApp Int [Exp]

    | ESet
    | EFun Exp Exp

    | Efun Int [(Name,Int,Exp)]       -- body of a definition

type Env = [Val]

update :: Env -> Val -> Env
update env u = u:env

getRef 0 (u:us) = u
getRef (n+1) (u:us) = getRef n us
getRef 0 [] = error "getRef"  -- this should never occur after scope analysis

eval :: Env -> Exp -> Val
eval env (ELam e)= Lam (\ u -> eval (update env u) e)
eval env (EApp n us) = apps (getRef n env) (map (eval env) us)
eval env ESet = Set
eval env (EFun a1 a2) =
 Fun (eval env a1) (\ u -> eval (update env u) a2)
eval env e = error "eval"

get s [] = error ("get " ++ s)     -- should never occur
get s ((s1,u):us) = if s == s1 then u else get s us

evalBody :: Env -> Val -> Exp -> Val

evalBody env v (ELam e) = Lam (\ u -> evalBody (update env u) (app v u) e)
evalBody env v (Efun k nes) =
 Lam f
  where
        f (App (Const c _) us) = apps (get c nvs) (drop k us)
        f w = app v w
        nvs = map (\ (c,_,e) -> (c,eval env e)) nes
evalBody env v e = eval env e
