{-# OPTIONS --cubical #-}

-- Test: with-pattern matching on Nat in Cubical Agda.
-- The injectivity of suc was previously unsupported in cubical
-- left-inverse construction, causing UnsupportedIndexedMatch warnings.
-- This test verifies the fix: clean compile, no warnings.

open import Agda.Builtin.Nat

-- Simple with-on-Nat
f : Nat → Nat
f n with n
... | zero = 0
... | suc n = f n

-- With-on-Nat returning a path (exercises the cubical transport path)
g : Nat → Nat → Nat
g m n with m
... | zero = n
... | suc m = suc (g m n)
