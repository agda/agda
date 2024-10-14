module UnquoteDefineDataOverFun where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Common.Reflection
open import Common.List

foo : ⊤
unquoteDef foo = do
  defineData foo []
