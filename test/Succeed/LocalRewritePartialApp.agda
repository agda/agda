{-# OPTIONS --local-rewriting  #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat

module LocalRewritePartialApp where

module Foo (f : Nat → Nat) (@rew ◆◆ : f 0 ≡ 1) where
  foo : Nat
  foo = 42

module Bar = Foo (λ _ → 0)
module Baz = Foo (λ _ → 1)

open Baz refl

test : Nat
test = foo
