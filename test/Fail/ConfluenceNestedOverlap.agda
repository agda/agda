{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  A : Set
  a b c : A
  f g : A → A

  rew₁ : f a ≡ b
  rew₂ : ∀ {x} → f (g x) ≡ c
  rew₃ : g a ≡ a

{-# REWRITE rew₁ #-}
{-# REWRITE rew₂ #-}
{-# REWRITE rew₃ #-}

works : (x : A) → f (g x) ≡ c
works x = refl

works' : f (g a) ≡ c
works' = works a

fails : f (g a) ≡ c
fails = refl
