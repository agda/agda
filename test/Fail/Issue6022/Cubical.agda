{-# OPTIONS --cubical #-}

module Issue6022.Cubical where

open import Agda.Primitive.Cubical renaming
  (primINeg to ~_; primIMax to _∨_; primIMin to _∧_;
  primHComp to hcomp; primTransp to transp; primComp to comp;
  itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path

{-# BUILTIN ID      Id   #-}
{-# BUILTIN REFLID  refl #-}

private primitive
  primDepIMin : _
  primIdFace  : ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → I
  primIdPath  : ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → x ≡ y
  primConId   : ∀ {ℓ} {A : Set ℓ} {x y : A} → I → x ≡ y → Id x y

-- These private primitives used to be nuked by dead-code elimination.
