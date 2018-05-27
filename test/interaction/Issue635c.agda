
open import Common.Prelude
open import Common.Equality
open import Common.Product

test : (p : Bool × Bool) → proj₁ p ≡ true → Set
test _ e = {!e!}

-- WAS:
-- Splitting on e gives
-- test r refl = ?
-- proj₁ r != true of type Bool
-- when checking that the pattern refl has type proj₁ r ≡ true

-- Expected: Splitting succeeds with
--   test _ refl = ?
