{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

-- Matching on variables that occur in local rewrite rules is not allowed!
module LocalRewriteBadMatch where

postulate
  f : Nat → Nat

module Foo (n : Nat) (@rew p : f n ≡ 0) where
  foo : n ≡ 42 → Nat
  foo refl = 0
