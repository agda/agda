module UnquoteBlocked where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Common.Reflection
open import Common.List

unquoteDecl foo = do
  mv ← checkType unknown (quoteTerm (TC ⊤))
  k ← unquoteTC {A = TC ⊤} mv
  k
