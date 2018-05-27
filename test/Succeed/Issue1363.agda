
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

postulate
  F : Set → Set

module M₀ where
  macro
    go-tactic₀ : Term → TC ⊤
    go-tactic₀ hole = unify hole (def (quote F) [])

  test₀ : Set
  test₀ = go-tactic₀ ⊤

module M₁ (A : Set) where
  macro
    go-tactic₁ : Term → TC ⊤
    go-tactic₁ hole = unify hole (def (quote F) [])

  test-inside-M₁ : Set
  test-inside-M₁ = go-tactic₁ ⊤

test-outside-M₁ : Set
test-outside-M₁ = M₁.go-tactic₁ ⊤ ⊤
