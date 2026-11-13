-- Andreas, 2016-07-28, issue #1720

{-# OPTIONS --allow-unsolved-metas --double-check #-}

record Foo (A : Set) : Set where
  a : A
  a = {!!} where
    a' : A
    a' = {!!}

  field
    f : A

-- Definitions with where clauses can precede a later field.
