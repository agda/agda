{-# OPTIONS --cubical-compatible #-}

module _ where

module M where
  data D : Set where

record R₁ : Set where
  field
    x : let module M′ = M in M′.D

variable
  A : Set

record R₂ (A : Set) : Set where

_ : (r : R₂ A) → let open R₂ r in Set₁
_ = λ _ → Set
