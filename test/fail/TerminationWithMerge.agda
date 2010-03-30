{-# OPTIONS --termination-depth=2 #-}

module TerminationWithMerge where

data List (a : Set) : Set where
  []  : List a
  _∷_ : a -> List a -> List a

-- infix

postulate 
  a : Set
  Bool : Set
  _≤?_ : a -> a -> Bool

merge : List a -> List a -> List a
merge xs           []           = xs
merge []           ys           = ys
merge (x ∷ xs) (y ∷ ys) with x ≤? y
... | true  = x ∷ merge xs  (y ∷ ys)
... | false = y ∷ merge (x ∷ xs) ys

{- still cannot pass the termination checker, since 

   size(x :: xs) <= 1 + max(size(x),size(xs))

but the termination checker does not have maximum, and no
type information that tells it to ignore x in this caculation.

Solution: sized types!
-}  