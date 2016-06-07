
module _ where

data Unit : Set where
  unit : Unit

module M (_ : Unit) where

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

open M unit

postulate
  A : Set

instance
  postulate
    m : R₁ A

a : A
a = x
