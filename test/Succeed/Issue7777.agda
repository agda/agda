-- Andreas, 2025-04-05, issue #7777
-- report and testcase by Alice Laroche

open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection

defaultTo : {A : Set} (x : A) → Term → TC ⊤
defaultTo x hole = bindTC (quoteTC x) (unify hole)

module Forall (P : .Bool → Set) (p : P true) where

  -- works
  f : ∀ {@(tactic defaultTo true) x} → P x
  f = p

  -- works
  g : ∀ {@irr @(tactic defaultTo true) x} → P x
  g = p

  -- should work
  h : ∀ .{ @(tactic defaultTo true) x} → P x
  h = p

-- works
f : {@(tactic defaultTo true) x : Bool} → Bool
f {x} = x

-- works
g : {@irr @(tactic defaultTo true) x : Bool} → Bool
g = true

-- should work
h : .{ @(tactic defaultTo true) x : Bool} → Bool
h = true
