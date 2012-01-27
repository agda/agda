------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic induction
------------------------------------------------------------------------

module Induction.Lexicographic where

open import Induction
open import Data.Product

-- The structure of lexicographic induction.

Σ-Rec : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} →
        RecStruct A → (∀ x → RecStruct (B x)) → RecStruct (Σ A B)
Σ-Rec RecA RecB P (x , y) =
  -- Either x is constant and y is "smaller", ...
  RecB x (λ y' → P (x , y')) y
    ×
  -- ...or x is "smaller" and y is arbitrary.
  RecA (λ x' → ∀ y' → P (x' , y')) x

_⊗_ : ∀ {ℓ} {A B : Set ℓ} →
      RecStruct A → RecStruct B → RecStruct (A × B)
RecA ⊗ RecB = Σ-Rec RecA (λ _ → RecB)

-- Constructs a recursor builder for lexicographic induction.

Σ-rec-builder :
  ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
    {RecA : RecStruct A}
    {RecB : ∀ x → RecStruct (B x)} →
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

[_⊗_] : ∀ {ℓ} {A B : Set ℓ} {RecA : RecStruct A} {RecB : RecStruct B} →
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
