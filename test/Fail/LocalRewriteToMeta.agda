{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat

module LocalRewriteToMeta where

nat : Nat
nat = {!!}

module _ (n : Nat) (@rew p : n ≡ nat) where
  test : Nat
  test = 42

test2 : 0 ≡ nat → Nat
test2 p = test 0 p
