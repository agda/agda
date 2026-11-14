-- Andreas, 2026-11-14, issue #8900, report and test case by @sshyou
-- Internal error with shared interaction meta in record field.

{-# OPTIONS --allow-unsolved-metas --double-check #-}

module _ where

open Agda.Primitive

-- Having two fields that share the type declaration
-- as well as interaction metas seems needed
record R (ℓ : Level) : Set ℓ where
  field X Y : ∀ {i} → ?

-- The hole depends on both binders.  Each reuse must skip all preceding
-- fields while retaining the variables bound inside the shared type.
record Dependent (A : Set) : Set₁ where
  field X Y Z : (B : A → Set) (a : A) → B (? a)

-- A field with the same name as a rechecked binder must not be selected
-- as an argument to the meta.  The inner shadowing also tests binding sites.
record Shadowing (A : Set) : Set₁ where
  field a B Y : (B : A → Set) (a : A) → B (? a)

record NestedShadowing (A : Set) : Set₁ where
  field a Y : (a : A) → ((a : A) → ? a) → Set

-- A variant without levels

data One : Set where tt : One
data All : One → Set where att : All tt

record Rec : Set where
  field X Y : (u : One) → All ?
