-- A variant of LostTypeError.
module LostTypeError2 where

postulate
  Wrap   : (A : Set) → (A → Set) → A → Set
  wrap   : (A : Set) (P : A → Set) (x : A) → P x → Wrap A P x
  rewrap : (A : Set) (P : A → Set) (x : A) → Wrap A P x → Wrap A P x

postulate A : Set

data Box : Set where
  box : A → Box

data Dummy : Set where
  box : Dummy

postulate
  x y : A
  P   : Box → Set
  Px  : P (box x)

bad : Wrap Box P (box y)
bad =
  rewrap _ (λ a → P _) (box y)
   (wrap _ (λ a → P _) (box x) Px)
