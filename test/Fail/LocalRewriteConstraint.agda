{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewriteConstraint where

module _ (x : Nat) (@rew _ : x ≡ 0) where
  foo : Nat
  foo = 0

bar : (x : Nat) → x ≡ 0 → Nat
bar x p = foo x p
