
open import Agda.Primitive

variable
  a : Level
  A : Set a
  P : A → Set a
  x : A

open import Agda.Builtin.Equality

data Box (A : Set a) : Set a where
  [_] : A → Box A

postulate
  _ : P (λ (_ : x ≡ x) → [ x ])
