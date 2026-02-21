{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewriteNested where

module Foo (n : Nat) (m : Nat) where
  module Bar (@rew p : n + m ≡ m) (l : Nat) where
    test : n + m ≡ m
    test = refl

open Foo 0 3
open Bar refl 42

test2 : 3 ≡ 3
test2 = test
