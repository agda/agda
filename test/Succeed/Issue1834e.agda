-- Andreas, 2016-04-18 Issue 1834 regression (extracted from larger test case)
{-# OPTIONS --guardedness #-}
-- {-# OPTIONS -v tc.cover:30 #-}

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

record Stream (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    head : A
    tail : Stream A
open Stream

weird' : (n : ℕ) → Stream ℕ
head (weird' zero)    = zero
tail (weird' zero)    = weird' zero
(     weird' (suc n)) = n ∷ tail (weird' n)
