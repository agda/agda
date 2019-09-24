{-# OPTIONS --safe #-}

module Issue2250-2 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data ⊥ : Set where

abstract

  f : Bool → Bool
  f x = true
  {-# INJECTIVE f #-}

  same : f true ≡ f false
  same = refl

not-same : f true ≡ f false → ⊥
not-same ()

absurd : ⊥
absurd = not-same same
