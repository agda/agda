-- Andreas, 2023-08-23
-- Trigger error DuplicateExecutable
--
-- See also:
-- * DuplicateExecutable.vars
-- * DuplicateExecutable/executables

{-# OPTIONS --allow-exec #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Reflection.External

macro
  echo : List String → Term → TC ⊤
  echo args hole = do
    (exitCode , (stdOut , stdErr)) ← execTC "echo" args ""
    unify hole (lit (string stdOut))

_ : echo ("hello" ∷ "world" ∷ []) ≡ "hello world\n"
_ = refl
