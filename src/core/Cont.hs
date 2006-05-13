module Cont where

import Val
import Exp
import Conv


-- all type-checking are done w.r.t. a stack of pairs (v,A)
-- values and type values. This is called a context

-- the scope analysis ensures that each deBruijn index has a value and a type value

type Cont = ([Val],[Val])

getVal n (env,tenv) = getRef n env
getType n (env,tenv) = getRef n tenv

upCon :: Val -> Val -> Cont -> Cont
upCon u a (env,tenv) = (u:env,a:tenv)

genCon :: Cont -> Name -> Val -> G Val
genCon (env,_) = gensym (length env) 

evalCon :: Cont -> Exp -> Val
evalCon (env,_) = eval env 

evalBodyCon :: Cont -> Val -> Exp -> Val
evalBodyCon (env,_) = evalBody env 

lastCon :: Cont -> G (Val,Val,Cont)
lastCon ([],_) = fail "lastCon"
lastCon (_,[]) = fail "lastCon"
lastCon (u:env,a:tenv) = return (u,a,(env,tenv))

lengthCon (env,_) = length env

