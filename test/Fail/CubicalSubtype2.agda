{-# OPTIONS --cubical --safe #-}
module CubicalSubtype2 where

open import Agda.Primitive renaming (_⊔_ to ℓ-max)
open import Agda.Primitive.Cubical renaming (primIMin to _∧_; primIMax to _∨_; primINeg to ~_; isOneEmpty to empty)
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to outS)

module _ {φ} {A : Set} {P : Partial φ A} (s : A) where
  _ : A [ φ ↦ P ]
  _ = s
  -- s != P
  -- included into partial element but φ ⊢ s ≠ P. so boundaries are
  -- preserved.
