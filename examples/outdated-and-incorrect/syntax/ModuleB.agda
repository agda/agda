
-- This module is used to illustrate how to import a parameterised module.
module examples.syntax.ModuleB
	(A : Set)
	((==) : A -> A -> Prop)
	(refl : (x : A) -> x == x)
    where

  infix 5 /\

  module SubModule where
    postulate dummy : A

  data True : Prop where
    tt : True

  data False : Prop where

  data (/\) (P, Q : Prop) : Prop where
    andI : P -> Q -> P /\ Q

  data List : Set where
    nil	  : List
    cons  : A -> List -> List

  eqList : List -> List -> Prop
  eqList nil         nil	  =  True
  eqList (cons x xs) nil          =  False
  eqList nil         (cons y ys)  =  False
  eqList (cons x xs) (cons y ys)  =  x == y /\ eqList xs ys

  reflEqList : (xs : List) -> eqList xs xs
  reflEqList nil	  = tt
  reflEqList (cons x xs)  = andI (refl x) (reflEqList xs)

