module Decl1 where

import Val
import Conv
import Core.Abs
import Exp1
import Cont
import Check

-- we can define only the last declared variable

-- data Decl = Var Name Exp | Def Name Exp Exp | Data Name Tel [(Name,Exp)] | DefRec Name Exp Exp

checkDecl :: Decl -> Cont -> G Cont

checkDecl (Var (s@(Ident n)) a) con =
 do
  checkT con a
  v <- return (evalCon con a)
  return (upCon s (mconst n v) v con)

checkDecl (Def s a e) con =
 do
  checkT con a
  v <- return (evalCon con a)
  check con v e
  u <- return (evalCon con e)
  return (upCon s u v con)

checkDecl (DefRec (s@(Ident n)) a e) con =
 do
  checkT con a
  v <- return (evalCon con a)
  check (upCon s (mconst n v) v con) v e
  return (mNewCon con v s e)

checkDecl (Data (s@(Ident n)) tel nas) con =
 do
  checkTel con tel
  v <- return (mSetTel (envCon con) tel)
  con1 <- return (upCon s (mPrim n v) v con)
  mVTCs tel con1 nas

mSetTel env [] = Set
mSetTel env ((Vcon x a):as) =
 Fun (eval env a) (\ u -> mSetTel (update env x u) as)

mNewCon con1 v (s@(Ident n)) e =
 newcon
  where
    w = evalBodyCon newcon (mconst n v) e
    newcon = upCon s w v con1

-- mDrop s k ((x1:A1,...,xk:Ak) -> A) is Fun (\ u1 -> ... \ uk -> mconst s A[u1,...,uk])
-- for representing the values of constructors with paramaters

mDrop (Ident n) 0 v = mPrim n v
mDrop s k (Fun _ f) = Lam (\ u -> mDrop s (k-1) (f u))

-- given c tel a build the value and the type of c
-- not efficient because we check again tel

mValTypCon :: Tel -> Cont -> Ident -> Exp -> G Cont

mValTypCon t con c a =
 do
  b <- return (mExpTel t a)
  checkT con b
  v <- return (evalCon con b)
  return (upCon c (mDrop c (length t) v) v con)

-- given tel and a list [(Name,Exp)] update the environment

mVTCs :: Tel -> Cont -> [ConstrDecl] -> G Cont

mVTCs t con [] = return con
mVTCs t con ((CDcon c a):rest) =
 do
  con1 <- mValTypCon t con c a
  mVTCs t con1 rest

type Tel = [VDecl]    -- telescopes

-- check telescopes

checkTel con [] = return ()
checkTel con ((Vcon x a):as) =
 do
  checkT con a
  v <- return (evalCon con a)
  u <- genCon con x v
  checkTel (upCon x u v con) as

-- mExpTel (a1,...,an) b = (x1:a1) -> (x2:a2) -> ... -> b

mExpTel [] b = b
mExpTel ((Vcon x a):as) b = EFun x a (mExpTel as b)


--- the main function: check a list of declarations

checkDs :: [Decl] -> Cont -> G Cont
checkDs [] con = return con
checkDs (d:ds) con =
 do
  con1 <- checkDecl d con
  checkDs ds con1
