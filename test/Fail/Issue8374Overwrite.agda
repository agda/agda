-- Andreas, 2026-02-07, issue #8374
-- Allow fixity declarations outside of anonymous modules.

infixr 20 _∷_

module _ (A : Set) where
  data List : Set where
    [] : List
    _∷_ : A → List → List

  -- This (incorrect) fixity overwrites the outer (correct) fixity.
  infixl 42 _∷_

-- This needs the correct fixity to type check:

dup : {A : Set} (a : A) → List A
dup a = a ∷ a ∷ []

-- Expected error: [UnequalTypes]
-- The type
--   List _A_9
-- is not a subtype of
--   A
-- when checking that the inferred type of an application
--   List _A_9
-- matches the expected type
--   A
