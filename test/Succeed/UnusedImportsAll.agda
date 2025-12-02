-- Andreas, 2025-11-30, AIM XLI, Angers, France
-- New warning UnusedImports, flavor 'all'.

{-# OPTIONS -WUnusedImports=all #-}

-- {-# OPTIONS --no-qualified-instances #-}
--   -- Instances have to be in scope unqualified,
--   -- so instances are always assumed to be used.

-- There should be no warning for the implicit
-- open import Agda.Primitive using (Set)

-- There should be no warning for public opens!
open import Agda.Builtin.Bool public

-- We are not using _≡_, so this opening is redundant.
-- (However, when we remove the 'using' clause then there is no warning,
-- since 'refl' is an instance.)
open import Agda.Builtin.Equality using (_≡_)

-- Expected warning:
-- Redundant opening of Agda.Builtin.Equality

-- We are not using everything we import, so there should be a warning.
open import Agda.Builtin.Nat using (zero; suc; _+_)

-- Expected warning:
-- Opening Agda.Builtin.Nat brings the following unused names into scope: _+_

-- This contains many useless imports, with the 'all' flavor we mention all of them.
open import Agda.Builtin.Nat renaming (Nat to Nat)

-- Opening Agda.Builtin.Nat brings the following unused names into
-- scope: _*_ _+_ _-_ _<_ _==_ div-helper mod-helper suc zero

-- We are using nothing from this import that is not already in scope,
-- so it should be redundant.
open import Agda.Builtin.Nat

-- Expected warning:
-- Redundant opening of Agda.Builtin.Nat

f : Nat → Nat
f zero = zero
f (suc n) = suc (f n)

module M where
  instance
    z : Nat
    z = zero

-- This brings instance z into scope, but we could use it qualified,
-- so there is a warning.
open M

-- Expected warning:
-- Redundant opening of M

g : {{x : Nat}} → Nat
g {{x}} = x

test : Nat
test = g  -- uses instance z

module Empty where

-- The module exports nothing so opening should be redundant.
open Empty

-- Expected warning:
-- Redundant opening of Empty
