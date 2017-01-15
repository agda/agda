-- Andreas, 2017-01-12, issue #2386

-- Should be rejected:
data Eq (A : Set) : (x y : A) → Set where
  refl : (x y : A) → Eq A x y

{-# BUILTIN EQUALITY Eq #-}

-- Expected error:
-- Wrong type of constructor of BUILTIN EQUALITY
-- when checking the pragma BUILTIN EQUALITY Eq
