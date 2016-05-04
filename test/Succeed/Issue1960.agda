-- Andreas, 2016-05-04, issue 1960 reported by Nisse

-- {-# OPTIONS -v tc.proj.amb:100 #-}

postulate
  A : Set

module M (_ : Set₁) where

  record R₁ : Set where
    field
      f : A

  open R₁ public

open M Set

record R₂ : Set where
  field
    f : A

open R₂ public

postulate
  P     : A → Set
  x     : R₁
  works : P (R₁.f x)
  test  : P   (f x)

-- should succeed
