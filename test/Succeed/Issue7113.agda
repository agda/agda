open import Agda.Builtin.Equality

record Semiring : Set₁ where
  field
    Carrier   : Set
    one       : Carrier
    mul       : Carrier → Carrier → Carrier
    left-unit : (r : Carrier) → mul one r ≡ r

open Semiring {{...}}



foo : {{R : Semiring}} (r : Carrier) → mul one r ≡ r
foo r with mul one r | left-unit r
...      | .r        | refl          = refl

