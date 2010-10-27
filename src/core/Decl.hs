module Decl where

import Val
import Conv
import Exp
import Cont
import Check

-- we can define only the last declared variable

data Decl = Var Name Exp | Def Name Exp | DefRec Name Exp

checkDecl :: Decl -> Cont -> G Cont
checkDecl (Var s a) con =
 do
  checkT con a
  v <- return (evalCon con a)
  return (upCon v (mconst s v) con)
checkDecl (Def s e) con =
 do
  (u,v,con1) <- lastCon con
  check con1 v e
  return (upCon (evalBodyCon con1 (mconst s v) e) v con1)
checkDecl (DefRec s e) con =
 do
  (_,v,con1) <- lastCon con
  check con v e
  return (mNewCon con1 v s e)

mNewCon con1 v s e =
 newcon
  where
    w = evalBodyCon newcon (mconst s v) e
    newcon = upCon w v con1
