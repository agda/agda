
-- This module is used to illustrate how to import a non-parameterised module.
module examples.syntax.ModuleA where

  data Nat : Set where
    zero  : Nat
    suc   : Nat -> Nat
    plus  : Nat -> Nat -> Nat

  eval : Nat -> Nat
  eval zero		    = zero
  eval (suc x)		    = suc (eval x)
  eval (plus zero y)	    = eval y
  eval (plus (suc x) y)	    = suc (eval (plus x y))
  eval (plus (plus x y) z)  = eval (plus x (plus y z))

