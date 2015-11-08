{-# OPTIONS --no-termination-check #-}
module Issue137 where

record Foo : Set1 where
  field
    foo : {x : Set} → Set

record Bar : Set1 where
  field
    bar : Foo

record Baz (P : Bar) : Set1 where
  field
    baz : Set

postulate
  P : Bar
  Q : Baz P

f : Baz.baz Q → Set
f r with f r
f r | A = A

-- The bug was:

-- Issue137.agda:22,1-12
-- Set should be a function type, but it isn't
-- when checking that the expression λ x → Foo.foo (Bar.bar P) {x} has
-- type Set

-- If the field foo is replaced by
--   foo : (x : Set) → Set
-- then the code type checks.
