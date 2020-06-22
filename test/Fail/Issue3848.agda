{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  A : Set
  a : A

record R : Set where
  constructor c
  field f : A
open R

postulate
  r : R
  rew₁ : ∀ x → c x ≡ r

{-# REWRITE rew₁ #-}

postulate
  g : A → A
  rew₂ : g (f r) ≡ a

{-# REWRITE rew₂ #-}

postulate
  rew₃ : f r ≡ a

{-# REWRITE rew₃ #-}
