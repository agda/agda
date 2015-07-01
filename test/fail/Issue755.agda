-- {-# OPTIONS -v tc.polarity:10 -v tc.conv.elim:25 #-}

module Issue755 where

open import Common.Prelude renaming (Nat to ℕ)
open import Common.Equality

abstract
  foo : Bool → ℕ → ℕ
  foo true  x = 0
  foo false x = 0

  -- should work
  works : ∀{b} → foo b 0 ≡ foo b 1 → foo b 0 ≡ foo b 1
  works refl = refl

-- should fail
test : ∀{b} → foo b 0 ≡ foo b 1 → foo b 0 ≡ foo b 1
test refl = refl
-- 0 != 1 of type ℕ
-- when checking that the pattern refl has type foo 0 ≡ foo 1
