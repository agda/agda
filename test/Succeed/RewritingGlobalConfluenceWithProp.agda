{-# OPTIONS --prop --rewriting --confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  A : Prop
  a : A
  B : Set
  b : B
  f : A → B → Set₁
  g : B → Set₁

  rew₁ : ∀ y → f a y ≡ g y
  rew₂ : ∀ x → f x b ≡ Set
  rew₃ : ∀ y → g y ≡ Set

{-# REWRITE rew₁ rew₂ rew₃ #-}
