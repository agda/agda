module Issue7797 where

data D : Set where
  c : D

record R (M : Set → Set) : Set₁ where
  field
    f : {A : Set} → A → M A

open R ⦃ … ⦄

postulate
  F : Set → Set

module M₁ (_ : Set₁) where

  postulate instance

    r : R F

open M₁ Set

module M₂ (A : Set) (_ : F A) where

open M₂ D (f c)
