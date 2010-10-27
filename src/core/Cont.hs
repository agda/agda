module Cont where

import Val
import Exp1
import Conv

-- all type-checking are done w.r.t. a stack of pairs (v,A)
-- values and type values. This is called a context

-- the scope analysis ensures that each deBruijn index has a value and a type value

type Cont = [(Name,Val,Val)]

envConv :: Cont -> Env
envConv = map (\ (s,u,_) -> (s,u))

getVal s ((s1,u,_):rest) = if s == s1 then u else getVal s rest
getVal s [] = error ("getRef " ++ s)  -- this should never occur after scope analysis

getType s ((s1,_,u):rest) = if s == s1 then u else getType s rest
getRef s [] = error ("getRef " ++ s)  -- this should never occur after scope analysis

upCon :: Name -> Val -> Val -> Cont -> Cont
upCon s u a con = (s,u,a):con

genCon :: Cont -> Name -> Val -> G Val
genCon con = gensym (length con)

evalCon :: Cont -> Exp -> Val
evalCon con = eval (envConv con)

evalBodyCon :: Cont -> Val -> Exp -> Val
evalBodyCon con = evalBody (envConv con)
