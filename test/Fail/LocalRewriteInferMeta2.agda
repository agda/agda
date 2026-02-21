{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewriteInferMeta2 where

module _ (f : Nat → Nat) (@rew p : f 0 ≡ 1) where
  foo : Nat
  foo = 0

  bar : Nat
  bar = 0

eta : _≡_ {A = _ → _} (foo λ n → n) (bar λ n → n)
eta = refl
