-- There was a bug with the new constraint machinery
-- where a type error could be ignored and checking
-- continued.
module LostTypeError where

postulate
  Wrap : (A : Set) (P : A → Set) → A → Set
  wrap : ∀ A (P : A → Set) (x : A) → P x → Wrap A P x
  A    : Set

data Box : Set where
  box : A → Box

data Dummy : Set where
  box : Dummy

postulate
  x y : A
  P   : Box → Set
  px  : P (box x)

bad : Wrap Box P (box y)
bad = wrap _ (λ a → P _) (box x) px
