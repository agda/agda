
module test.simple where

module Nat where

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

  (+) : Nat -> Nat -> Nat
  zero + m = m
  suc n + m = suc (n + m)

data List (A:Set) : Set where
  nil : List A
  cons : A -> List A -> List A

mutual
  data Even : Set where
    evenZero : Even
    evenSuc  : Odd -> Even

  data Odd : Set where
    oddSuc : Even -> Odd

data Monad (m:Set -> Set) : Set1 where
  monad : ((a:Set) -> a -> m a) ->
	  ((a,b:Set) -> m a -> (a -> m b) -> m b) ->
	  Monad m

postulate
  return : {m:Set -> Set} -> {a:Set} -> Monad m -> a -> m a

infix 5 ==

postulate
  (==) : {A:Set} -> A -> A -> Prop
  refl : {A:Set} -> {a:A} -> a == a

open Nat

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

open Stack
open Ops

zzz = push zero (unit (suc zero))

{-
postulate
  A   : Set
--   idA : A -> A
--   F   : Set -> Set
--   H   : (A,B:Set) -> Prop
--   id  : (A:Set) -> A -> A
--   idH : {A:Set} -> A -> A
--   fa  : F A
  a   : A

-- test1 = id (F A) fa
-- test2 = idH fa
-- test3 = id _ fa
-- test4 = idH {! foo bar !}
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
-}
