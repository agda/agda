module Check where

import Val
import Conv
import Exp1
import Cont

-- checking the correctness of a type, and of an expression

check :: Cont -> Val -> Exp -> G ()
checkT :: Cont -> Exp -> G ()

checkT con ESet = return ()
checkT con (EFun a b) =
 do
  checkT con a
  v <- return (evalCon con a)
  u <- genCon con "X" v
  checkT (upCon u v con) b
checkT con e = check con Set e

-- check a body of a definition

check con (Fun v f) (ELam e) =
 do
  u <- genCon con "X" v
  check (upCon u v con) (f u) e
check con v (EApp n es) =
 do
  v' <- checkI con (getType n con) es
  eqT (lengthCon con) v v'
check con v (Efun nes) =
 mapM_ (checkP con v) nes
check _ _ _ = fail "check"

checkP con (Fun (App h ps) f) (_,i,e) =
 do
  v <- return (getVal i con)
  w <- return (getType i con)
  check con (itCurry (apps v ps) (inst w ps) f) e
checkP _ _ _ = fail "checkP"

-- check a vector of exps against an iterated function type

checkI con (Fun a f) (e:es) =
 do
  check con a e
  checkI con (f (evalCon con e)) es
checkI _ v []  = return v
checkI _ _ _   = fail "checkI"
