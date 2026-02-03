{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewriteMatch where

module _ (x : Nat) {@rew _ : x ≡ 1} _ where
  foo : x ≡ 0 → Nat
  foo refl = {!!}
