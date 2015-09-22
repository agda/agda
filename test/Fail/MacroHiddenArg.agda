module MacroHiddenArg where

open import Common.Reflection

macro
  f : (t : Term) -> {a : Term} -> Term
  f x = x
