{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewriteMeta where

module _ (x : Nat) (@rew _ : x ≡ 0) where
  foo : Nat
  foo = 0

bar : (x : Nat) → Nat
bar x = foo x {!!}
