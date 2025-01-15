-- Andreas, 2024-01-03, issue #7669
-- Report and test case by Szumi Xie.
--
-- Positivity checker computed arity not up to definitional equality.

data Unit : Set where
  tt : Unit

FUN : Set₁
FUN = Set → Set

-- The arity of Id should not depend on the use of abbreviation FUN.
-- I.e., it should be 2, not 1.

Id : Unit → FUN
Id tt A = A

-- The positivity checker should know that
-- Id is strictly positive in its second argument.

data Nat : Set where
  zero : Nat
  suc : (x : Unit) → Id x Nat → Nat

-- WAS: error: [NotStrictlyPositive]
-- Nat is not strictly positive, because it occurs
-- in the second argument of Id
-- in the type of the constructor suc
-- in the definition of Nat.

-- Should succeed.
