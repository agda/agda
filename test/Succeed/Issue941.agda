-- Pattern synonyms are now allowed in parameterised modules.

module _ where

module L (A : Set) where
  data List : Set where
    nil : List
    cons : A → List → List
  pattern singleton x = cons x nil

data Bool : Set where
  true false : Bool

module LB = L Bool
open LB

init : List → List
init nil = nil
init (singleton _) = nil
init (cons x xs) = cons x (init xs)

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

test : init (cons true (singleton false)) ≡ singleton true
test = refl
