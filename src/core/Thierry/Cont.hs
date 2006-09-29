module Cont where

import Val
import Core.Abs
import Exp1
import Conv

-- all type-checking are done w.r.t. a stack of pairs (v,A)
-- values and type values. This is called a context

-- the scope analysis ensures that each deBruijn index has a value and a type value

type Cont = [(Ident,Val,Val)]

envCon :: Cont -> Env
envCon = map (\ (s,u,_) -> (s,u))

getVT s ((s1,u,v):rest) = if s == s1 then (u,v) else getVT s rest
getVT s [] = error ("getVT " ++ show s)  -- this should never occur after scope analysis

upCon :: Ident -> Val -> Val -> Cont -> Cont
upCon s u a con = (s,u,a):con

genCon :: Cont -> Ident -> Val -> G Val
genCon con (Ident s) = gensym (length con) s

evalCon :: Cont -> Exp -> Val
evalCon con = eval (envCon con)

evalBodyCon :: Cont -> Val -> Exp -> Val
evalBodyCon con = evalBody (envCon con)
