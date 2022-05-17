module _ where

open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

module Test₁ where

  macro

    Unify-with-⊤ : Term → TC ⊤
    Unify-with-⊤ goal = unify goal (quoteTerm ⊤)

  ⊤′ : Set
  ⊤′ = Unify-with-⊤

  unit-test : ⊤′
  unit-test = tt

module Test₂ where

  macro

    Unify-with-⊤ : Term → TC ⊤
    Unify-with-⊤ goal = noConstraints (unify goal (quoteTerm ⊤))

  ⊤′ : Set
  ⊤′ = Unify-with-⊤

  unit-test : ⊤′
  unit-test = tt

module Test₃ where

  P : Bool → Set
  P true  = Bool
  P false = Bool

  f : (b : Bool) → P b
  f true  = true
  f false = false

  pattern varg x =
    arg (arg-info visible (modality relevant quantity-ω)) x

  create-constraint : TC Set
  create-constraint =
    unquoteTC (def (quote P)
                 (varg (def (quote f) (varg unknown ∷ [])) ∷ []))

  macro

    Unify-with-⊤ : Term → TC ⊤
    Unify-with-⊤ goal =
      catchTC (noConstraints (bindTC create-constraint λ _ →
                              returnTC tt))
              (unify goal (quoteTerm ⊤))

  ⊤′ : Set
  ⊤′ = Unify-with-⊤

  unit-test : ⊤′
  unit-test = tt
