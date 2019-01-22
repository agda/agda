{-# OPTIONS --without-K #-}
module Common.Product where

open import Common.Level

infixr 4 _,_ _,′_
infixr 2 _×_

------------------------------------------------------------------------
-- Definition

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∶ A ] B

_,′_ : ∀ {a b} {A : Set a} {B : Set b} → A → B → A × B
_,′_ = _,_
