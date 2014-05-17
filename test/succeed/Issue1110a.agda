-- Andreas, 2014-05-17

open import Common.Prelude
open import Common.Equality

test : Nat
test rewrite refl = zero
