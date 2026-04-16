{-# OPTIONS --local-rewriting  #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat

module LocalRewritePartialApp where

module Foo (f : Nat → Nat) (@rewrite ◆◆ : f 0 ≡ 1) where
  foo : Nat
  foo = 42

-- Even though we haven't applied the local rewrite argument yet, we still need
-- to throw an error because of how module applications get eta-expanded
module Bar = Foo (λ _ → 0)
