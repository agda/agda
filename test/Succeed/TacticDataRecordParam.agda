{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

tac : Term → TC ⊤
tac hole = unify hole (lit (nat 42))

data Foo {@(tactic tac) n : Nat} : Set where
  foo : Foo {n}

mkFoo : Foo {42}
mkFoo = foo

record Bar {@(tactic tac) n : Nat} : Set where
  constructor bar

mkBar : Bar {42}
mkBar = bar

data Baz {@(tactic tac) n : Nat} : Set

data Baz {@(tactic tac) n : Nat} where
  baz : Baz {n}

mkBaz : Baz {42}
mkBaz = baz
