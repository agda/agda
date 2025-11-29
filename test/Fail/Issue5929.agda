{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Unit

postulate
  f : {X : Set} → X → Set
  g : {X : Set} → Set → X

postulate
  rew-fg : {X : Set} (A : Set) → f {X} (g {X} A) ≡ A
{-# REWRITE rew-fg #-}
