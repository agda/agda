-- Andreas, 2026-09-02, issue #8545, reported by carlostome.
--
-- The data type `D` is reached via two nested module copies:
-- `open M ... public` only supplies the first of M's parameters,
-- and `open R r` then instantiates the record module.
-- Unfolding the copy chain got stuck on the underapplied intermediate copy,
-- so `checkParameters` compared the parameters of unrelated data type copies.

{-# OPTIONS --no-fast-reduce #-} -- crashes also with --fast-reduce

record TC : Set2 where
  field Foo : Set1

instance
  _ : TC
  _ = record { Foo = Set }

record S : Set₁ where
  field K : Set

module M (s : S) (open S s) ⦃ _ : TC ⦄ where
  data D : Set where
    c : K → D

-- Just some type.
postulate Unit : Set

record R : Set₁ where
  field dummy : Set
  open M (record { K = Unit }) public

r : R
r = record { dummy = Unit }
open R r

f : D → Set₁
f (c k) = Set
