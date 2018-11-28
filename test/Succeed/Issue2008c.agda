{-# OPTIONS --overlapping-instances #-}

module _ where

record R (_ : Set) : Set where

r : ∀ {X} → R X
r = record {}

module M (_ : ∀ {X} → R X) where

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

open M r

postulate
  A : Set

instance
  postulate
    m : R₁ A

a : A
a = x
