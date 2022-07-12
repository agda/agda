-- Auxiliary module for issue #5989

-- {-# OPTIONS -v tc.dead:100 #-}

module Issue5989.Import where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.List

private
  trivial-tactic : Term -> TC ⊤
  trivial-tactic hole = unify hole (con (quote zero) [])

use-tactic : (a : Nat) -> {@(tactic trivial-tactic) x : Nat} -> Nat
use-tactic a = a

three : Nat
three = use-tactic 3
