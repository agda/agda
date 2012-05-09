-- Andreas, 2012-05-09
module DontPrune where

open import Common.Equality
open import Common.Product

data Bool : Set where
  true false : Bool

test : (A : Set) →
  let IF : Bool → A → A → A
      IF = _
  in  (a b : A) →
      (IF true a b ≡ a) × (IF false a b ≡ b)
test A a b = refl , refl

-- Expected result: unsolved metas
--
-- (unless someone implemented unification that produces definitions by case).
--
-- The test case should prevent overzealous pruning:
-- If the first equation pruned away the b, then the second
-- would have an unbound rhs.
