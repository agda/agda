module QualifiedIdiom where

module Y where postulate
  N     : Set → Set
  _<*>_ : ∀ {A B} → N (A → B) → N A → N B
  pure  : ∀ {A} → A → N A
  empty : ∀ {A} → N A
  _<|>_ : ∀ {A} → N A → N A → N A

open Y using (N)

postulate
  A B C : Set
  a a' a'' : N A
  b : N B
  g : A → B
  f : A → B → C

_ : N C
_ = Y.⦇ f a b ⦈

_ : N A
_ = Y.(|)

_ : N B
_ = Y.(| g a | g a' | g a'' |)
