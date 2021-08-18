-- Andreas, 2021-08-18, issue #5506 reported by alexarice

-- A crash in the forcing methodology introduced in 2.6.1
-- that surfaced with the removal of auto-inlining in 2.6.2.

-- {-# OPTIONS --no-forcing #-}   -- fixes
-- {-# OPTIONS --auto-inline #-}  -- fixes

{-# OPTIONS -v tc.lhs.unify.force:100 #-}

open import Agda.Builtin.Nat

data Unit : Set where
  unit : Unit

data Ctx : Nat → Set where  -- index needed
  cons : (m : Nat) (A : Unit) → Ctx (suc m)

mutual

  data P : (n : Nat) (Γ : Ctx n) → Set

  -- Needs to be mutual
  {-# NOINLINE getFocus #-}
  getFocus : (n : Nat) (A : Unit) → Unit
  getFocus n A = A  -- needs to be A, not unit

  data P where
    c : (n : Nat)  -- n is forced
        (A : Unit)
      → P (suc n) (cons n (getFocus n A))

test : (n : Nat) (Γ : Ctx n) → P n Γ → Nat
test n Γ (c m A) = n + m
  -- ^ n := suc m fixes the issue

-- WAS:
-- Panic: Pattern match failure in do expression at
-- src/full/Agda/TypeChecking/Rules/LHS/Unify.hs:1313:7-14
-- when checking that the pattern c _ _ _ _ has type P n Γ

-- Expect: type-checks without errors.
