{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewriteConstraint2 where

module Foo (x : Nat) (@rewrite p : x ≡ 1) where
  foo : Nat
  foo = 0

postulate
  nat  : Nat
  nat0 : nat ≡ 0

open Foo nat nat0
