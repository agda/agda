open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

@0 A : Set₁
A = Set

macro

  @0 m : Term → TC ⊤
  m B =
    bindTC (quoteTC A) λ A →
    unify A B

B : Set₁
B = m
