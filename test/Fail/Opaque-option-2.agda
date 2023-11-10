{-# OPTIONS --opaque #-}

open import Agda.Builtin.Equality

module _ where

module M where

  F : Set₁ → Set₁
  F A = A

  _ : F Set ≡ Set
  _ = refl
