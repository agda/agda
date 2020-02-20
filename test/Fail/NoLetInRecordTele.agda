open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

record R {A : Set} {B : A → Set} p@ab : Set where
  field
    prf : p ≡ p
