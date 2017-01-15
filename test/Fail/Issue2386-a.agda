-- Andreas, 2017-01-12, issue #2386

postulate
  A : Set

-- Should be rejected:
data Eq : (B : Set) (x y : B) → Set where
  refl : (x : A) → Eq A x x

{-# BUILTIN EQUALITY Eq #-}

-- Expected error:
-- Wrong type of constructor of BUILTIN EQUALITY
-- when checking the pragma BUILTIN EQUALITY Eq
