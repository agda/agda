{-# OPTIONS --hidden-argument-puns -vtc.instance:30 #-}
module Issue7846 where

open import Agda.Builtin.Equality

record R₁ (F : Set → Set) : Set₁ where
  field
    f : {A : Set} → F A → A

record R₂ (A : Set) : Set where
  field
    x : A

record R₃ (A : Set) : Set where
  field
    x : A

  r : R₂ A
  r = record { x = x }

instance

  r₂ : R₁ R₂
  r₂ = record { f = R₂.x }

  r₃ : R₁ R₃
  r₃ = record { f = R₃.x }

P :
  {A : Set} {F₁ F₂ : Set → Set} ⦃ r₁ : R₁ F₁ ⦄ ⦃ r₂ : R₁ F₂ ⦄ →
  F₁ A → F₂ A → Set
P ⦃ r₁ ⦄ ⦃ r₂ ⦄ x y = R₁.f r₁ x ≡ R₁.f r₂ y

Q :
  {F₁ F₂ : Set → Set} ⦃ r₁ : R₁ F₁ ⦄ ⦃ r₂ : R₁ F₂ ⦄
  (A : Set) → (F₁ A → F₂ A) → Set
Q {F₁} A f = (x : F₁ A) → P (f x) x

opaque
  _ : (A : Set) → Q A R₃.r
  _ = λ _ _ → refl
