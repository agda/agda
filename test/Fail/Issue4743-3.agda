-- An example involving the "sharp" function.

{-# OPTIONS --guardedness --erasure #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Coinduction

mutual

  x : ∞ Bool
  x = _

  @0 _ : x ≡ ♯ true
  _ = refl
