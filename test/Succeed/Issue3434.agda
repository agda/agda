module _ where

data Unit : Set where
  unit : Unit

data D₁ : Set where
  c₁ : D₁

module M (_ : Set₁) where

  data D₂ : Set where
    c₂ : D₂

open M Set

f : D₁ → D₂
f c₁ = c₂

record R (A : Set) : Set where
  field a : A

open R ⦃ … ⦄ public

instance

  r₁ : R D₁
  r₁ = record { a = c₁ }

  r₂ : ⦃ r : R D₁ ⦄ → R D₂
  r₂ ⦃ r ⦄ = record { a = f (R.a r) }

postulate
  P : (A : Set) → A → Set
  g : (A : Set) (x : A) → P A x

accepted : P D₂ a
accepted = g D₂ a

rejected : P D₂ a
rejected = g _ a

-- WAS:
--   No instance of type (R D₂) was found in scope.
--   when checking that the expression a has type D₂
-- SHOULD: succeed
