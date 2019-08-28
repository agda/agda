{-# OPTIONS --without-K --rewriting -v rewriting:50 #-}

open import Agda.Primitive using (Level; _⊔_; Setω; lzero; lsuc)

module Issue4020 where

data _≡_ {ℓ : Level} {A : Set ℓ} (a : A) : A → Set ℓ where
  refl : a ≡ a

{-# BUILTIN REWRITE _≡_ #-}

ap : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {a₁ a₂} → a₁ ≡ a₂ → f a₁ ≡ f a₂
ap f refl = refl

ap-const-Set : ∀ {a b} {A : Set a} {a₁ a₂ : A} (p : a₁ ≡ a₂) → ap (\ _ → Set b) p ≡ refl
ap-const-Set refl = refl

{-# REWRITE ap-const-Set #-}
{- /home/jason/bug.agda:18,1-29
ap-const-Set  is not a legal rewrite rule, since the following variables are not bound by the left hand side:  b
when checking the pragma REWRITE ap-const-Set -}
