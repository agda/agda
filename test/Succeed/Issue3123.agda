
open import Agda.Primitive

record Setoid (a : Level) : Set₁ where
  constructor mk
  field
    carrier : Set

record HeytingAlgebra {a} (setoid : Setoid a) (A : Set) : Set a where
  constructor laws
  open Setoid setoid
  field ∧-cong : carrier
