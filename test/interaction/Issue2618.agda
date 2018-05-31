
open import Agda.Builtin.List
open import Agda.Builtin.Reflection

macro

  print : (Set → Set) → Term → TC _
  print t _ = bindTC (quoteTC t) λ t →
              typeError (termErr t ∷ [])

-- Prints λ { X → X }.

Test₁ : Set
Test₁ = {!print (λ { X → X })!}

module _ (A : Set) where

  -- Prints λ { A₁ X → X }.

  Test₂ : Set
  Test₂ = {!print (λ { X → X })!}

  -- Prints λ { B₁ X → X } B.

  Test₃ : Set → Set
  Test₃ B = {!print (λ { X → X })!}

module _ (A : Set) where

  -- Prints λ { A₁ X → A₁ }. Note that A is not mentioned at all.

  Test₄ : Set
  Test₄ = {!print (λ { X → A })!}

  -- Prints λ { B₁ X → A } B.

  Test₅ : Set → Set
  Test₅ B = {!print (λ { X → A })!}
