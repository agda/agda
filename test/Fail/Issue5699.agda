{-# OPTIONS --show-implicit #-}

open import Agda.Builtin.Reflection renaming ( bindTC to _>>=_ )
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Primitive

macro
  test : Term → Term → TC ⊤
  test argument _ = do
    evaluated ← withReconstructed true (reduce argument)
    typeError (termErr evaluated ∷ [])

module _ {ℓ} where
  data Foo (R : Set ℓ → Set ℓ) : Set ℓ where
    bar : Foo R

foo : ⊤
foo = test bar
