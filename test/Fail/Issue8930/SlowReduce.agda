-- Andreas, 2026-11-19, issue #8390, report and test by Ode-to-a-Nightingale
-- Discrepancy in float semantics for slow and fast reduction leads to inconsistency

-- To reproduce #8390, this needs to be checked with slow reduction.

{-# OPTIONS --safe --no-fast-reduce #-}

module Issue8930.SlowReduce where

open import Agda.Builtin.Float
open import Agda.Builtin.Equality

-- Checked with the slow reducer: primFloatACosh is evaluated with cosh.
-- This produced a number (1.543...) different from the correct result:
-- acosh 1 is zero, according to the formula
-- acosh(x) = ln(x + √(x² - 1)) for x ≥ 1.

acosh1slow : primFloatACosh 1.0 ≡ 1.5430806348152437
acosh1slow = refl

-- This should fail with the correct implementation of acosh.
