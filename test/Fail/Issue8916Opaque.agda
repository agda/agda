module Issue8916Opaque where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

record R (A : Set) : Set where
  opaque
    field a : A
    b : A
    b = a
    field c : A

-- Fields reduce, but the internal definition must remain opaque.
r : R Nat
r = record { a = 1; c = 2 }

_ : R.b r ≡ R.a r
_ = refl
