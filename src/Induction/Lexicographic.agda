------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic induction
------------------------------------------------------------------------

module Induction.Lexicographic where

open import Data.Product
open import Induction
open import Level

-- The structure of lexicographic induction.

Σ-Rec : ∀ {a b ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : A → Set b} →
        RecStruct A (ℓ₁ ⊔ b) ℓ₂ → (∀ x → RecStruct (B x) ℓ₁ ℓ₃) →
        RecStruct (Σ A B) _ _
Σ-Rec RecA RecB P (x , y) =
  -- Either x is constant and y is "smaller", ...
  RecB x (λ y' → P (x , y')) y
    ×
  -- ...or x is "smaller" and y is arbitrary.
  RecA (λ x' → ∀ y' → P (x' , y')) x

_⊗_ : ∀ {a b ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} →
      RecStruct A (ℓ₁ ⊔ b) ℓ₂ → RecStruct B ℓ₁ ℓ₃ →
      RecStruct (A × B) _ _
RecA ⊗ RecB = Σ-Rec RecA (λ _ → RecB)

-- Constructs a recursor builder for lexicographic induction.

Σ-rec-builder :
  ∀ {a b ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : A → Set b}
    {RecA : RecStruct A (ℓ₁ ⊔ b) ℓ₂}
    {RecB : ∀ x → RecStruct (B x) ℓ₁ ℓ₃} →
  RecursorBuilder RecA → (∀ x → RecursorBuilder (RecB x)) →
  RecursorBuilder (Σ-Rec RecA RecB)
Σ-rec-builder {RecA = RecA} {RecB = RecB} recA recB P f (x , y) =
  (p₁ x y p₂x , p₂x)
  where
  p₁ : ∀ x y →
       RecA (λ x' → ∀ y' → P (x' , y')) x →
       RecB x (λ y' → P (x , y')) y
  p₁ x y x-rec = recB x
                      (λ y' → P (x , y'))
                      (λ y y-rec → f (x , y) (y-rec , x-rec))
                      y

  p₂ : ∀ x → RecA (λ x' → ∀ y' → P (x' , y')) x
  p₂ = recA (λ x → ∀ y → P (x , y))
            (λ x x-rec y → f (x , y) (p₁ x y x-rec , x-rec))

  p₂x = p₂ x

[_⊗_] : ∀ {a b ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b}
          {RecA : RecStruct A (ℓ₁ ⊔ b) ℓ₂} {RecB : RecStruct B ℓ₁ ℓ₃} →
        RecursorBuilder RecA → RecursorBuilder RecB →
        RecursorBuilder (RecA ⊗ RecB)
[ recA ⊗ recB ] = Σ-rec-builder recA (λ _ → recB)

------------------------------------------------------------------------
-- Example

private

  open import Data.Nat
  open import Induction.Nat as N

  -- The Ackermann function à la Rózsa Péter.

  ackermann : ℕ → ℕ → ℕ
  ackermann m n =
    build [ N.rec-builder ⊗ N.rec-builder ]
          (λ _ → ℕ)
          (λ { (zero  , n)     _                   → 1 + n
             ; (suc m , zero)  (_         , ackm•) → ackm• 1
             ; (suc m , suc n) (ack[1+m]n , ackm•) → ackm• ack[1+m]n
             })
          (m , n)
