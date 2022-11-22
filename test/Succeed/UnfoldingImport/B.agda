module UnfoldingImport.B where

open import Agda.Builtin.Equality
open import UnfoldingImport.A

abstract unfolding (y) where
  z : x
  z = 123

  _ : z ≡ y
  _ = refl
