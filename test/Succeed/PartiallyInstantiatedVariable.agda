

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

record R : Set where
  field
    r1 r2 : Nat

test : (x : R) → R.r1 x ≡ 0 → Nat
test x refl = 0
