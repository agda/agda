module Issue6962Pattern where

open import Agda.Builtin.Nat
f (n@(suc m) : Nat) : Nat
f = m
