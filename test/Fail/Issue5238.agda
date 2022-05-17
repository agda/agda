{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data ⊥ : Set where

postulate
  T : Set
  t0 : T
  t1 : T

postulate
  foo : ⊥ → t0 ≡ t1
  {-# REWRITE foo #-}

test : t0 ≡ t1
test = refl
