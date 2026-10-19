{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

tac : Term → TC ⊤
tac hole = unify hole (lit (nat 42))

module _ {@(tactic tac) n : Nat} where
  data D : Set where
    c : D
test : D
test = c {41}

-- Curiously, if we instead provide an explicit argument to `D` this typechecks.
-- This is a bit surprising to me, but seems relatively harmless.
-- > test : D {41}
-- > test = c
