module MacroNotToTerm where

open import Common.Reflection

data X : Set where


macro
  f : Term -> Set
  f x _ = X
