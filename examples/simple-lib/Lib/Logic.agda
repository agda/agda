
module Lib.Logic where

infix 30 _∨_
infix 40 _∧_
infix 50 ¬_

data _∨_ (A B : Set) : Set where
  inl : A -> A ∨ B
  inr : B -> A ∨ B

data _∧_ (A B : Set) : Set where
  _,_ : A -> B -> A ∧ B

data   False : Set where
record True  : Set where

¬_ : Set -> Set
¬ A = A -> False