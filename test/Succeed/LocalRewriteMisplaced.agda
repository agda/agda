{-# OPTIONS --local-rewriting --erasure #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat

module LocalRewriteMisplaced where

-- Eventually @rewrite on declarations should be supported as alternative an
-- alternative for {-# REWRITE #-} pragmas
-- All other uses should probably remain warnings
postulate
  @rewrite test : ∀ {x} → x + 0 ≡ x

@rewrite test2 : ∀ {x} → x + 0 ≡ x
@rewrite test2 = test

variable
  @rewrite p : ∀ {x} → x + 0 ≡ x

data @rewrite Foo : Set where
  @rewrite mk : Foo

record @rewrite Bar : Set where
  field
    @rewrite proj : Foo

test3 : Nat → Nat
test3 x = let postulate @rewrite p : x ≡ 0 in 42
