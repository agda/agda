
module Issue643 where

module M₁ (A : Set) where

  record R : Set₁ where
    field
      P : A → Set

module M₂ (A : Set) where

  open M₁ A

  postulate
    r : R
    T : R → Set

  open R r

  p : ∀ x → P x
  p x = {!!}     -- The goal was printed as "P" rather than "P x".

  q : T r
  q = {!!}       -- This goal was printed as T P at an intermediate stage of fixing
