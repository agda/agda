{-# OPTIONS --copatterns #-}
-- Andreas, 2013-11-05  Coverage checker needs clauses to reduce type!
-- {-# OPTIONS -v tc.cover:20 #-}

module Issue937a where

open import Common.Prelude
open import Common.Equality
open import Common.Product

T : (b : Bool) → Set
T true = Nat
T false = Bool → Nat

test : Σ Bool T
proj₁ test = false
proj₂ test true  = zero
proj₂ test false = suc zero -- Error: unreachable clause

module _ {_ : Set} where

  bla : Σ Bool T
  proj₁ bla = false
  proj₂ bla true  = zero
  proj₂ bla false = suc zero -- Error: unreachable clause

-- should coverage check
