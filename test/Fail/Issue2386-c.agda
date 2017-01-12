-- Andreas, 2017-01-12, issue #2386

postulate
  F : ∀{a}{A : Set a} → A → A

data Eq (A : Set) : (x y : F A) → Set where
  refl : (x : F A) → Eq A x x

{-# BUILTIN EQUALITY Eq #-}

-- Expected error:
-- The type of BUILTIN EQUALITY must be a polymorphic relation
-- when checking the pragma BUILTIN EQUALITY Eq
