{-# OPTIONS --cubical --safe #-}
module CubicalSubtype1 where

open import Agda.Primitive renaming (_⊔_ to ℓ-max)
open import Agda.Primitive.Cubical renaming (primIMin to _∧_; primIMax to _∨_; primINeg to ~_; isOneEmpty to empty)
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to outS)
open import Agda.Builtin.Cubical.Path

module _ {φ} {A B : Set} {P : Partial φ A} (s : A [ φ ↦ P ]) where
  _ : B
  _ = s
  -- A !≤ B
  -- projected the partial element but does not let us cheat the type
  -- checker (ok, it doesn't let us cheat the type checker *that* much)
