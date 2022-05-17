{-# OPTIONS --cubical-compatible --rewriting #-}

open import Agda.Primitive using (Level; _⊔_; Setω; lzero; lsuc)

module Issue4020b where

data _≡_ {ℓ : Level} {A : Set ℓ} (a : A) : A → Set ℓ where
  refl : a ≡ a

{-# BUILTIN REWRITE _≡_ #-}

ap : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {a₁ a₂} → a₁ ≡ a₂ → f a₁ ≡ f a₂
ap f refl = refl

ap-const-Pi : ∀ {a b} {A : Set a} {B : A → Set b} {a₁ a₂ : A} (p : a₁ ≡ a₂) → ap (\ _ → (x : A) → B x) p ≡ refl
ap-const-Pi refl = refl

{-# REWRITE ap-const-Pi #-}
{- /home/jason/bug2.agda:18,1-28
ap-const-Pi  is not a legal rewrite rule, since the following variables are not bound by the left hand side:  b
when checking the pragma REWRITE ap-const-Pi -}
