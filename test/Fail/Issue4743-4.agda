-- An example involving an absurd lambda.

{-# OPTIONS --erasure #-}

open import Agda.Builtin.Equality

data ⊥ : Set where

mutual

  h : ⊥ → Set
  h = _

  @0 _ : h ≡ λ ()
  _ = refl
