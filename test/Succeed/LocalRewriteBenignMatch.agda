{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewriteBenignMatch where

postulate
  f : Nat → Nat

module Foo (n : Nat) (m : Nat) (@rew p : f n ≡ 0) (q : f m ≡ 0) where
  foo : m ≡ 42 → f 42 ≡ 0
  foo refl = q
