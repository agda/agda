{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path

postulate
  trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z

infix  -1 finally
infixr -2 _≡⟨⟩_

_≡⟨⟩_ : {A : Set} (x {y} : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

finally : {A : Set} (x y : A) → x ≡ y → x ≡ y
finally _ _ x≡y = x≡y

syntax finally x y x≡y = x ≡⟨ x≡y ⟩∎ y ∎

⟨_⟩ : {A : Set} → A → A
⟨ x ⟩ = x

{-# NOINLINE ⟨_⟩ #-}

record R (F : Set → Set) : Set₁ where
  field
    p : {A : Set} {x : F A} → x ≡ x

open R ⦃ … ⦄ public

test :
  {F : Set → Set} ⦃ r : R F ⦄ {A : Set} {x₁ x₂ : F A}
  (p₁ p₂ : x₁ ≡ x₂) (assumption : p₁ ≡ p₂) →
  trans p p₁ ≡ trans p p₂
test p₁ p₂ assumption =
  trans p p₁      ≡⟨⟩
  trans p ⟨ p₁ ⟩  ≡⟨ ? ⟩∎  -- The goal type should contain ⟨_⟩.
  trans p p₂      ∎
