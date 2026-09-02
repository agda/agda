-- Andreas, 2026-09-02, issue #8545, variants of the original test case.

module Issue8545b where

record TC : Set where

instance
  _ : TC
  _ = record {}

postulate Unit : Set

-- Without the `open` in the module telescope,
-- the same problem used to produce a bogus type error
-- rather than an internal error.

module Plain where

  module M (X : Set) ⦃ _ : TC ⦄ where
    data D : Set where
      c : X → D

  record R : Set₁ where
    field dummy : Set
    open M Unit public

  r : R
  r = record { dummy = Unit }
  open R r

  f : D → Set₁
  f (c k) = Set

-- Without the `dummy` field, so that `R` is an eta-record.

module NoField where

  record S : Set₁ where
    field K : Set

  module M (s : S) (open S s) ⦃ _ : TC ⦄ where
    data D : Set where
      c : K → D

  record R : Set₁ where
    open M (record { K = Unit }) public

  r : R
  r = record {}
  open R r

  f : D → Unit
  f (c k) = k
