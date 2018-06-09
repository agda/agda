-- Andreas & James, 2016-04-18 pre-AIM XXIII
-- order of clauses should not matter here!

{-# OPTIONS --exact-split #-}

open import Common.Prelude

record R (A : Set) : Set where
  field out : A

T : (x y : Bool) → Set
T true y     = R Bool
T false true = R Nat
T false false = R String

test : (x y : Bool) → T x y
R.out (test true  y)     = y
R.out (test false true ) = 0
R.out (test false false) = "hallo"
