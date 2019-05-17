{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

postulate
  A : Set
  u₁ u₂ : ⊤

mutual
  X : (⊤ → ⊤) → A
  X = _

  test : X (λ x → u₁) ≡ X (λ x → u₂)
  test = refl
