{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

module TacticModuleParam where

tac : Term → TC ⊤
tac hole = unify hole (lit (nat 42))

module _ {@(tactic tac) n : Nat} where
  foo : Nat
  foo = 0

test : Nat
test = foo
