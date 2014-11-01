-- Andreas, 2014-11-01 reported by twanvl

data ℕ : Set where
  zero : ℕ

module Mod₁ (n : ℕ) where
  Thing : Set
  Thing = ℕ

module Mod₂ (n : ℕ) where

  open Mod₁ zero

  record Foo : Set where
    field
      foo : Thing → Thing

    bar : Thing → Thing
    bar a with foo a
    ... | x = x

-- As of 2014-11-01, error on maint is:
-- Expected a visible argument, but found a hidden argument
-- when checking that the type (a : Thing) → Thing → Thing of the
-- generated with function is well-formed

-- Succeeds on master.
