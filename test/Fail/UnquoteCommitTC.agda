module UnquoteCommitTC where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Common.Reflection
open import Common.List

unquoteDecl foo = do
  tt ← declareDef (vArg foo) (quoteTerm ⊤)
  commitTC
