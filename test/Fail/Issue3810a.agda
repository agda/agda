{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  A : Set
  a b : A
  f : A → A
  rew₁ : f a ≡ b
  rew₂ : f ≡ λ _ → a

{-# REWRITE rew₁ #-}
{-# REWRITE rew₂ #-}
