open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

macro

  @0 m : Set → Term → TC ⊤
  m A B =
    bindTC (quoteTC A) λ A →
    unify A B

F : @0 Set → Set
F A = m A
