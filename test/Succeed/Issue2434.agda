{-# OPTIONS --exact-split -v tc.cover.cover:100 #-}

open import Common.Bool
open import Common.Equality

record Unit : Set where
  eta-equality
  constructor unit

f : Unit → Bool → Bool
f unit true  = true
f u    false = false  -- passes without --exact-split

-- All equations pass do hold definitionally:

test-1 : f unit true ≡ true
test-1 = refl

test-2 : ∀{u : Unit} → f u false ≡ false
test-2 = refl

-- Error:
-- Exact splitting is enabled, but not all clauses can be preserved as
-- definitional equalities in the translation to a case tree
-- when checking the definition of f

-- Should succeed.
