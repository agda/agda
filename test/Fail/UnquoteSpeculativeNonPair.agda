module UnquoteSpeculativeNonPair where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Common.Reflection
open import Common.List

unquoteDecl foo = do
  extendContext "foo" (vArg (quoteTerm (Σ ⊤ λ _ → Bool))) do
    val ← unquoteTC {A = Σ ⊤ λ _ → Bool} (var 0 [])
    runSpeculative (returnTC val)
