-- Andreas, 2014-05-17

open import Common.Prelude
open import Common.Equality

postulate
  bla : ∀ x → x ≡ zero
  P   : Nat → Set
  p   : P zero
  K   : ∀{A B : Set} → A → B → A


f : ∀ x → P x
f x rewrite K {x ≡ x} {Nat} refl {!!} = {!!}

-- Expected: two interaction points!
