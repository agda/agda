-- Andreas, 2026-08-21, issue #8599, shrunk to not use the standard library.
--
-- The pattern of an irrefutable @with@ bind (@with p ← e@) was not parsed
-- correctly if @p@ was a single name that is also in scope as a record field:
-- the LHS parser only considered @p@ as a projection (copattern)
-- and gave up with a @NoParseForLHS@ error.
--
-- In the original example, the offending name was @refl@, in scope both as
-- constructor @_≡_.refl@ and as field @Setoid.refl@ (via @open Setoid S@).
-- Note that the field alone was enough to trigger the problem;
-- neither the ambiguity nor the constructor are needed.

{-# OPTIONS --cubical-compatible --safe #-}

module Issue8599 where

-- Note: the record has to be declared before @refl@ is brought into scope
-- by the import below, lest we get a @ClashingDefinition@ error.

record Setoid : Set₁ where
  field
    Carrier : Set
    refl    : Carrier   -- Cf. @Setoid.refl@ in the standard library.

open import Agda.Builtin.Equality using (_≡_; refl)

module _ (S : Setoid) where

  open Setoid S  -- Brings field @refl@ into scope, unqualified.

  -- Matching on the constructor @refl@ in an ordinary clause works:

  ok : (x y : Carrier) (eq : x ≡ y) → Carrier
  ok x y refl = x

  -- The same pattern in an irrefutable @with@ bind did not parse:

  test : (x y : Carrier) (eq : x ≡ y) → Carrier
  test x y eq
    with refl ← eq
    = x
