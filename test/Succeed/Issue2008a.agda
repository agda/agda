{-# OPTIONS --overlapping-instances #-}

module _ where

module M (_ : Set₁) where

  record R₁ (A : Set) : Set₁ where
    no-eta-equality

    postulate
      x : A

  open R₁ ⦃ … ⦄ public

  record R₂ (A : Set) : Set₁ where
    field
      instance
        r₁ : R₁ A

  open R₂ ⦃ … ⦄

open module MSet = M Set

postulate
  A : Set

instance
  postulate
    m : R₁ A

a : A
a = x
