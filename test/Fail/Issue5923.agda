{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Unit

postulate
  A : Set
  a : A
  f : {X : Set} → X → A
  g : {X : Set} → A → X
  rew-fg : {X : Set} (a : A) → f (g {X} a) ≡ a
{-# REWRITE rew-fg #-}

test : f tt ≡ a
test = refl
