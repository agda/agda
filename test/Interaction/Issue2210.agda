module _ where

record R : Set₁ where
  field
    Type : Set

postulate
  A : Set

module M (x : A) (r₁ : R) (y : A) where

  open R r₁

  r₂ : R
  r₂ = record { Type = A }

  foo : R.Type r₂
  foo = {!!}  -- R.Type r₂

  bar : R.Type r₁
  bar = {!!}  -- Type
