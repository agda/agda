-- {-# OPTIONS -v tc.lhs.top:90 #-}
-- {-# OPTIONS -v tc.match:60 #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record R : Set₁ where
  field
    fun  : (A : Set) → A → Bool → A ≡ Bool → Bool
    rule : ∀ x → fun Bool false x refl ≡ false
open R

test : R
test .fun .Bool true true refl = true
test .fun _     _    _    _    = false
test .rule x = refl

-- Expected error: [UnequalTerms]
-- The terms
--   test .fun Bool false x refl
-- and
--   false
-- are not equal at type Bool
-- when checking that the expression refl has type
-- test .fun Bool false x refl ≡ false

-- The equation
--
--   test .fun Bool false x refl = false
--
-- is not definitional because the generated splittree
-- happens to split on x before splitting on refl.
-- (Left to right splitting order when possible.)
