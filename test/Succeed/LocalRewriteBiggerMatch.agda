{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewriteBiggerMatch where

module Foo (f g : Nat → Nat) (n : Nat) (@rewrite p : f (g n) ≡ 0) where
  test : f (g n) ≡ 0
  test = refl
