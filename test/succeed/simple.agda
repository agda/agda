{-# OPTIONS --allow-unsolved-metas #-}

module simple where

module Nat where

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

  _+_ : Nat -> Nat -> Nat
  zero  + m = m
  suc n + m = suc (n + m)

module N = Nat

z  = N._+_ (N.suc N.zero) (N.suc N.zero)
zz = Nat._+_ (Nat.suc Nat.zero) (Nat.suc Nat.zero)

module List (A : Set) where

  infixr 15 _::_ _++_

  data List : Set where
    nil  : List
    _::_ : A -> List -> List

  _++_ : List -> List -> List
  nil       ++ ys = ys
  (x :: xs) ++ ys = x :: (xs ++ ys)

module TestList where

  open Nat
  module ListNat = List Nat
  open ListNat using (_++_; _::_; nil)

  zzz = (zero :: nil) ++ (suc zero :: nil)

module EvenOdd where

  mutual
    data Even : Set where
      evenZero : Even
      evenSuc  : Odd -> Even

    data Odd : Set where
      oddSuc : Even -> Odd

module Monad where

  data Monad (m : Set -> Set) : Set1 where
    monad : ({a : Set} -> a -> m a) ->
            ({a b : Set} -> m a -> (a -> m b) -> m b) ->
            Monad m

  return : {m : Set -> Set} -> {a : Set} -> Monad m -> a -> m a
  return (monad ret _) x = ret x

module Stack where

  abstract
    data Stack (A : Set) : Set where
      snil : Stack A
      scons : A -> Stack A -> Stack A

  module Ops where

    abstract
      empty : {A : Set} -> Stack A
      empty = snil

      push : {A : Set} -> A -> Stack A -> Stack A
      push x s = scons x s

    unit : {A : Set} -> A -> Stack A
    unit x = push x empty

module TestStack where

  open Stack using (Stack)
  open Stack.Ops
  open Nat

  zzzz : Stack Nat
  zzzz = push zero (unit (suc zero))

module TestIdentity where

  postulate
    A   : Set
    idA : A -> A
    F   : Set -> Set
    H   : (A B : Set) -> Set
    id0 : (A : Set) -> A -> A
    idH : {A : Set} -> A -> A
    fa  : F A
    a   : A

  test1 = id0 (F A) fa
  test2 = idH fa
  test3 = id0 _ fa
  test4 = idH {! foo bar !}
  -- test5 = id id      -- we can't do this (on purpose)!

  id = \{A : Set}(x : A) -> x
  test = id a

module prop where

  postulate
    _\/_  : Set -> Set -> Set
    inl   : {P Q : Set} -> P -> P \/ Q
    inr   : {P Q : Set} -> Q -> P \/ Q
    orE   : {P Q R : Set} -> P \/ Q -> (P -> R) -> (Q -> R) -> R
    False : Set
    _==>_ : Set -> Set -> Set
    impI  : {P Q : Set} -> (P -> Q) -> P ==> Q
    impE  : {P Q : Set} -> P ==> Q -> P -> Q

  Not = \(P : Set) -> P ==> False

  notnotEM = \(P : Set) ->
    impI (\ (nEM : Not (P \/ Not P)) ->
            impE nEM (
                inr (
                  impI (\ p ->
                    impE nEM (inl p)
                  )
                )
              )
            )

module Tests where

  infix 5 _==_
  postulate
    _==_ : {A : Set} -> A -> A -> Set
    refl : {A : Set} -> {x : A} -> x == x

  open TestList.ListNat
  open Nat

  test1 : TestList.zzz == zero :: suc zero :: nil
  test1 = refl

