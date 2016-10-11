{-# OPTIONS --termination-depth=2 #-}

module TerminationWithMerge where

data List (a : Set) : Set where
  []  : List a
  _∷_ : a -> List a -> List a

open import Agda.Builtin.Bool

postulate
  a : Set
  _≤?_ : a -> a -> Bool

merge : List a -> List a -> List a
merge xs           []           = xs
merge []           ys           = ys
merge (x ∷ xs) (y ∷ ys) with x ≤? y
... | true  = x ∷ merge xs  (y ∷ ys)
... | false = y ∷ merge (x ∷ xs) ys
