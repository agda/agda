{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

module TacticModuleParam where

tac : Term → TC ⊤
tac hole = unify hole (lit (nat 42))

module Foo {@(tactic tac) n : Nat} where
  foo : Nat
  foo = 0

test : Nat
test = Foo.foo

test2 : Nat
test2 = foo
  where open Foo
