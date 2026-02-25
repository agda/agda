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

module _ (n : Nat) (@rew p : n ≡ {!!}) where
  test2 : n ≡ _
  test2 = refl

test3 : 0 ≡ nat → Nat
test3 p = test 0 p
