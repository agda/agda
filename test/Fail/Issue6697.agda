{-# OPTIONS --rewriting #-}

data _≅_ {a} {A : Set a} (x : A) : ∀ {b} {B : Set b} → B → Set a where
   refl : x ≅ x

infix 4 _≡_
_≡_ : ∀ {ℓ} {A B : Set ℓ} → A → B → Set ℓ
x ≡ y = x ≅ y

{-# BUILTIN REWRITE _≡_ #-}

