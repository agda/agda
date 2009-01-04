------------------------------------------------------------------------
-- Lexicographic induction
------------------------------------------------------------------------

module Induction.Lexicographic where

open import Induction
open import Data.Product

-- The structure of lexicographic induction.

_⊗_ : ∀ {a b} → RecStruct a → RecStruct b → RecStruct (a × b)
_⊗_ RecA RecB P (x , y) =
  -- Either x is constant and y is "smaller", ...
  RecB (λ y' → P (x , y')) y
    ×
  -- ...or x is "smaller" and y is arbitrary.
  RecA (λ x' → ∀ y' → P (x' , y')) x

-- Constructs a recursor builder for lexicographic induction.

[_⊗_] : ∀ {a} {RecA : RecStruct a} → RecursorBuilder RecA →
        ∀ {b} {RecB : RecStruct b} → RecursorBuilder RecB →
        RecursorBuilder (RecA ⊗ RecB)
[_⊗_] {RecA = RecA} recA {RecB = RecB} recB P f (x , y) =
  (p₁ x y p₂x , p₂x)
  where
  p₁ : ∀ x y →
       RecA (λ x' → ∀ y' → P (x' , y')) x →
       RecB (λ y' → P (x , y')) y
  p₁ x y x-rec = recB (λ y' → P (x , y'))
                      (λ y y-rec → f (x , y) (y-rec , x-rec))
                      y

  p₂ : ∀ x → RecA (λ x' → ∀ y' → P (x' , y')) x
  p₂ = recA (λ x → ∀ y → P (x , y))
            (λ x x-rec y → f (x , y) (p₁ x y x-rec , x-rec))

  p₂x = p₂ x

------------------------------------------------------------------------
-- Example

private

  open import Data.Nat
  open import Induction.Nat as N

  -- The Ackermann function à la Rózsa Péter.

  ackermann : ℕ → ℕ → ℕ
  ackermann m n = build [ N.rec-builder ⊗ N.rec-builder ]
                        AckPred ack (m , n)
    where
    AckPred : ℕ × ℕ → Set
    AckPred _ = ℕ

    ack : ∀ p → (N.Rec ⊗ N.Rec) AckPred p → AckPred p
    ack (zero  , n)     _                   = 1 + n
    ack (suc m , zero)  (_         , ackm•) = ackm• 1
    ack (suc m , suc n) (ack[1+m]n , ackm•) = ackm• ack[1+m]n
