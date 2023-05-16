{-# OPTIONS --cubical #-}
module PruneINeg where

open import Agda.Primitive renaming (Set to Type)
open import Agda.Primitive.Cubical renaming (primIMin to _∧_; primIMax to _∨_; primINeg to ~_; isOneEmpty to empty)
open import Agda.Builtin.Cubical.Path

refl : ∀ {ℓ₁} {A : Type ℓ₁} {x : A} → x ≡ x
refl {x = x} i = x

sym : ∀ {ℓ₁} {A : Type ℓ₁} {x y : A}
    → x ≡ y → y ≡ x
sym p i = p (~ i)

module _ {A : Set} {x y : A} (p : x ≡ y) where
  _ : sym p ≡ sym _
  _ = refl
  -- Need to solve a constraint like _ (~ i) := p (~ i) by expanding
  -- (~ i) := t into i := ~ t in the meta spine
