module Issue434Private where

record R : Set₁ where
  field A : Set

  private
    identity : A → A
    identity a = a

  field a : A

bad = R.identity
