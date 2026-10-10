{-# OPTIONS --safe --without-K #-}

-- Issue #8704: non-abstract (non-opaque) metavariables can be solved while
-- checking an abstract (opaque) definition if the solution is also well-typed
-- in the original context of the meta.
--
-- The solution might be non-unique when viewed from outside the abstract
-- (opaque) block, though.  This leaks the implementation of abstract (opaque)
-- definitions, but does not compromise consistency.

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

mutual
  -- `secret` is definitionally equal to `false`, but only inside abstract
  -- blocks.
  abstract
    secret : Bool
    secret = false

  -- The meta `_` could be solved with either `secret` or `false`, which are
  -- not equal since `Test` is not abstract.
  Test : Set
  Test = secret ≡ _

  -- `test` instantiates the meta with `false`, which is unique in the
  -- context of `test` but non-unique in the original context of the meta.
  abstract
    test : Test
    test = refl

-- Variant with opaque.

dummy : Bool
dummy = true where
  opaque
    secret' : Bool
    secret' = false

  opaque
    Test' : Set
    Test' = secret' ≡ _

  opaque
    unfolding secret' Test'

    test' : Test'
    test' = refl
