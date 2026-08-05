module Issue7627 where

module Done where
  -- checking case trees that have only Done
  f : {A : Set} (a b c : A) -> A
  f a b c = a

  g : {A B C : Set} (a : A) (b : B) (c : C) -> B
  g a b c = b

  h : {A : Set} (a : A) {B : A -> Set} (b : B a) -> B a
  h a b = b

module Case where
  -- checking case trees that split on an inductive datatype
  data Nat : Set where
    Z : Nat
    S : Nat -> Nat

  f : Nat -> Nat -> Nat
  f Z m = m
  f (S n) m = n

module Fail where
  -- checking case trees that have an absurd case
  data False : Set where

  f : False -> False
  f ()

module Coinduction where
  -- checking case trees that split on the result
