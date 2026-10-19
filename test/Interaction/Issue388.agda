{-# OPTIONS --cubical-compatible #-}
module Issue388 where

data P (A : Set₁) : A → Set₁ where
  p : ∀ x → P A x

data D : Set → Set₁ where
  d : ∀ A → D A

Foo : ∀ A → P (D A) (d A) → Set
Foo A x = {!x!}
