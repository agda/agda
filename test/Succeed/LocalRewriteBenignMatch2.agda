{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat

module LocalRewriteBenignMatch2 where

data Foo : Nat → Set where
  foo : ∀ {n} → Foo n

module Bar (f : ∀ {n} → Foo n → Foo n)
           (@rew p : ∀ {n} {x : Foo n} → f x ≡ x) where
  test : ∀ {m} (x : Foo m) → f x ≡ foo
  test foo = refl


module Baz (f : ∀ {n} → Foo n → Foo n) (k : Nat) (l : Nat)
           (@rew p : ∀ {n} {x : Foo n} → f x ≡ x) where
  test : ∀ {m} (x : Foo m) → f x ≡ foo
  test foo = refl
