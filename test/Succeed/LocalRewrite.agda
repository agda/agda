{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewrite where

module Foo (n : Nat) (m : Nat) (@rew p : n + m ≡ m) (l : Nat) where
  test : n + m ≡ m
  test = refl

test2 : 3 ≡ 3
test2 = Foo.test 0 3 refl 42
