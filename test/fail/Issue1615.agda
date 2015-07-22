-- Andreas, 2015-07-22

-- {-# OPTIONS -v tc.term:20 -v tc.meta.assign:10 -v tc.conv.coerce:10 #-}

open import Common.Size

data Nat (i : Size) : Set where
  suc  : (j : Size< i) → Nat j → Nat i

min : ∀ i → Nat i → Nat i → Nat i
min i (suc j n) (suc k m) = suc i' (min i' n m)
  where i' = _

-- Size consistency check should not be circumvented
-- by putting the meta in a definition.
