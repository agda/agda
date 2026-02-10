{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma

module LocalRewriteVarLHS where

postulate
  Vec : Nat → Set

module Foo (n : Nat) (@rew p : n ≡ 0) where
  test : Nat
  test = 42

  test2 : Vec _ → Vec n
  test2 x = x
