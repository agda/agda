module MacroHiddenArg where

open import Common.Reflection
open import Common.TC

macro
  f : (t : Term) -> {a : Term} -> Tactic
  f x = x
