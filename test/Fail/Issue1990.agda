{-# OPTIONS --rewriting #-}

data _≅_ {ℓ} {A : Set ℓ} (x : A) : {B : Set ℓ} → B → Set where
  refl : x ≅ x

{-# BUILTIN REWRITE _≅_ #-}
