{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewriteBenignMatch where

postulate
  f : Nat → Nat

module Foo (n : Nat) (m : Nat) (@rew p : f n ≡ 0)  where
  foo : m ≡ 42 → Nat
  foo refl = 0
