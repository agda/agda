-- Andreas, 2019-02-23, issue #3578.
-- Preserve types as much as possible during pattern matching.
-- New unifier (from Agda 2.5.1) was normalizing too much.

-- {-# OPTIONS -v tc.lhs.unify:45 #-}

data Nat : Set where
  zero : Nat

postulate
  MustNotBeNamed : Set

A = MustNotBeNamed

data P : Nat → Set where
  z : A → P zero

test : ∀{n} → P n → Set
test (z x) = {!x!}   -- C-c C-,

-- EXPECTED:
--
-- Goal: Set
-- ——————————————
-- x : A
