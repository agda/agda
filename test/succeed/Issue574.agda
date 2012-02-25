-- Andreas, 2012-02-25 reported by edgmnt on behalf of xplat.
module Issue574 where

open import Level

wah : ∀ o a → Set (suc zero ⊔ (suc a ⊔ o)) → Set ((suc zero ⊔ suc a) ⊔ o)
wah o a x = x -- should succeed

-- Error message was:
-- Set (suc zero ⊔ (suc a ⊔ o)) != Set (suc a ⊔ o)
-- when checking that the expression x has type Set (suc a ⊔ o)