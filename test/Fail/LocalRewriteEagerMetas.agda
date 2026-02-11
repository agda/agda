{-# OPTIONS --rewriting  #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

-- Test case by Jesper Cockx
module LocalRewriteEagerMetas where

-- Hack to stop "foo"s meta getting frozen
MUTUAL : Set₁

foo : (Nat → Nat) → Nat → Nat
foo f x = _

module M (f : Nat → Nat) (x : Nat) (@rew r : f x ≡ 0) where

  solve : foo f x ≡ 0
  solve = refl

MUTUAL = Set
