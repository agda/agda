module _ where

module M₁ (_ : Set) where

  postulate
    A : Set

record R : Set₁ where
  field
    A : Set

module M₂ (r : R) where

  open M₁ (R.A r) public

module Unused (A : Set) (_ : Set) where

  open M₁ A public

postulate
  r : R

open M₂ r

postulate
  P : A → Set

data D : Set where
  c : D

F : D → Set
F c = A

_ : ∀ x → F x → Set
_ = λ _ r → P r
