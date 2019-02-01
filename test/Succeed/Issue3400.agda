module _ where

module M₁ where

  record R : Set₂ where
    field
      _A : Set₁

  open R

  -- The following code used to be syntactically incorrect, because
  -- the left-hand side could be parsed either as the function r
  -- applied to a pattern variable, or as the copattern _A applied
  -- to r. Now the former interpretation is ruled out.

  r : R
  r A = Set

module M₂ where

  record R : Set₂ where
    field
      _A : Set₁

  open R

  data D : Set where
    d_A : D

  -- Name parts coming from constructors can be used as part of
  -- copatterns.

  r : R
  r A = Set

module M₃ where

  data D₂ : Set where
    c : D₂

  record R₂ : Set₁ where
    field
      f_c : Set

  open R₂

  -- Name parts coming from projections can be used as part of
  -- constructor patterns.

  F : D₂ → Set₁
  F c = Set
