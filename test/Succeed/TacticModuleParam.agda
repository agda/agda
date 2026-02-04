{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

module TacticModuleParam where

tac : Term → TC ⊤
tac hole = unify hole (lit (nat 42))

-- Explicitly not-injective function so Agda can't cheat by relying on
-- unification
f : Nat → Nat
f zero    = 0
f (suc n) = 0


module Foo {@(tactic tac) n : Nat} where
  foo : Nat
  foo = f n

test : Nat
test = Foo.foo

test-eq : test ≡ f 42
test-eq = refl

test2 : Nat
test2 = foo
  where open Foo

test2-eq : test2 ≡ f 42
test2-eq = refl
