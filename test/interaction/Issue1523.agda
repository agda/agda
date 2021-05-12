-- Andreas, 2015-07-22  Fixed bug in test for empty type of sizes

{-# OPTIONS --copatterns --sized-types #-}

open import Common.Size

record U (i : Size) : Set where
  coinductive
  field out : (j : Size< i) → U j
open U

fixU : {A : Size → Set} (let C = λ i → A i → U i)
  → ∀ i (f : ∀ i → (∀ (j : Size< i) → C j) → C i) → C i
out (fixU i f a) j = out (f i {!λ (j : Size< i) → fixU j f!} a) j

-- Giving should succeed (even if termination checking might not succeed yet)
