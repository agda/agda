module MacroNotToTerm where

open import Common.Reflection
open import Common.Prelude

data X : Set where


macro
  f : Term → Set
  f x = X
