-- Andreas, 2014-08-28, reported by Jacques Carette

{-# OPTIONS --cubical-compatible #-}

-- {-# OPTIONS -v term:20 #-}

module _ where

data Bool : Set where true false : Bool

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

module Sort (A : Set) ( _≤_ : A → A → Bool) where

  insert : A → List A → List A
  insert x [] = []
  insert x (y ∷ ys) with x ≤ y
  ... | true = x ∷ (y ∷ ys)
  ... | false = y ∷ insert x ys

-- Should termination check.
-- (Did not because while with lhss were not inlined, with-calls still were.)
