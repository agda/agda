module Issue7227 where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Common.Reflection
open import Common.List

unquoteDecl foo = do
  v0 ← extendContext "foo" (vArg (quoteTerm Nat)) do
    unquoteTC {A = Nat} (var 0 [])
  typeError (termErr (lit (nat v0)) ∷ [])
