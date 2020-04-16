open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

not : Bool → Bool
not true  = false
not false = true

macro

  apply′ : Term → Term → Term → TC ⊤
  apply′ f x goal =
    bindTC (inferType f) λ t →
    bindTC (apply t f
              (arg (arg-info hidden relevant) x ∷ [])) λ (_ , t) →
           unify goal t

b : Bool
b = apply′ not false
