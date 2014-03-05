-- Andreas, 2014-03-05, reported by xcycl.xoo, Mar 30, 2009
-- {-# OPTIONS -v tc.with:60 #-}

open import Common.Prelude renaming (Nat to ℕ; module Nat to ℕ)

data Nat : ℕ → Set where
  i : (k : ℕ) → Nat k

toNat : (n : ℕ) → Nat n
toNat n = i n

fun : (n : ℕ) → ℕ
fun n with toNat n
fun .m | i m with toNat m
fun .Set | i .l | i l = 0
