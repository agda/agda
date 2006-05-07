
module test.simple where

module Nat where

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

  (+) : Nat -> Nat -> Nat
  zero + m = m
  suc n + m = suc (n + m)

module List where

  data List (A:Set) : Set where
    nil : List A
    cons : A -> List A -> List A

module EvenOdd where

  mutual
    data Even : Set where
      evenZero : Even
      evenSuc  : Odd -> Even

    data Odd : Set where
      oddSuc : Even -> Odd

module Monad where

  data Monad (m:Set -> Set) : Set1 where
    monad : ({a:Set} -> a -> m a) ->
	    ({a,b:Set} -> m a -> (a -> m b) -> m b) ->
	    Monad m

  return : {m:Set -> Set} -> {a:Set} -> Monad m -> a -> m a
  return {_} {a} (monad ret _) x = ret x

module Stack where

  abstract
    data Stack (A:Set) : Set where
      snil : Stack A
      scons : A -> Stack A -> Stack A

  module Ops where

    abstract
      empty : {A:Set} -> Stack A
      empty {A} = snil

      push : {A:Set} -> A -> Stack A -> Stack A
      push {A} x s = scons x s

    unit : {A:Set} -> A -> Stack A
    unit {A} x = push x empty

module TestStack where

  open Stack, using (Stack)
  open Stack.Ops
  open Nat

  zzz = push zero (unit (suc zero))

module TestIdentity where

  postulate
    A   : Set
    idA : A -> A
    F   : Set -> Set
    H   : (A,B:Set) -> Prop
    id0 : (A:Set) -> A -> A
    idH : {A:Set} -> A -> A
    fa  : F A
    a   : A

  test1 = id0 (F A) fa
  test2 = idH fa
  test3 = id0 _ fa
  test4 = idH {! foo bar !}
  -- test5 = id id	-- we can't do this (on purpose)!

  id = \{A:Set}(x:A) -> x

  test = id a

module prop where

  postulate
    (\/)  : Prop -> Prop -> Prop
    inl	  : {P,Q:Prop} -> P -> P \/ Q
    inr	  : {P,Q:Prop} -> Q -> P \/ Q
    orE	  : {P,Q,R:Prop} -> P \/ Q -> (P -> R) -> (Q -> R) -> R
    False : Prop
    (==>) : Prop -> Prop -> Prop
    impI  : {P,Q:Prop} -> (P -> Q) -> P ==> Q
    impE  : {P,Q:Prop} -> P ==> Q -> P -> Q

  Not = \(P:Prop) -> P ==> False

  notnotEM = \(P:Prop) ->
    impI (\ (nEM : Not (P \/ Not P)) ->
	    impE nEM (
		inr (
		  impI (\ p ->
		    impE nEM (inl p)
		  )
		)
	      )
	    )

