-- Andreas, 2014-05-17

open import Common.Prelude
open import Common.Equality

postulate
  bla : ∀ x → x ≡ zero
  P   : Nat → Set
  p   : P zero

f : ∀ x → P x
f x rewrite bla {!!} = {!!}

-- Expected: two interaction points!
