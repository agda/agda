{-# OPTIONS --allow-exec #-}

module ExecAgda where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Reflection.External

macro
  test : Term → TC ⊤
  test hole = execTC "agda" ("-v0" ∷ "-i" ∷ "test/Succeed" ∷ "test/Succeed/exec-tc/empty.agda" ∷ []) ""
          >>= λ{(exitCode , (stdOut , stdErr)) → unify hole (lit (string stdOut))}

_ : test ≡ ""
_ = refl
