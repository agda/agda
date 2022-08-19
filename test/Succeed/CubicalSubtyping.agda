{-# OPTIONS --cubical --safe #-}
module CubicalSubtyping where

open import Agda.Primitive renaming (_⊔_ to ℓ-max)
open import Agda.Primitive.Cubical renaming (primIMin to _∧_; primIMax to _∨_; primINeg to ~_; isOneEmpty to empty)
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to outS)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Glue renaming (primGlue to Glue; prim^glue to glue; prim^unglue to unglue)
open Helpers

module _ {φ} {A : Set} {P : Partial φ A} (s : A [ φ ↦ P ]) where
  -- Can project implicitly:
  _ : A
  _ = s

  -- Can project explicitly:
  _ : A
  _ = outS s

  -- Can refer as extension type:
  _ : A [ φ ↦ P ]
  _ = s

_ : {ℓ : Level} {A : Set ℓ} {w x y z : A}
  → w ≡ x → x ≡ y → y ≡ z → I → A
_ = λ p q r i →
  hfill (λ { j (i = i0) → p (~ j) ; j (i = i1) → r j }) (q i) i
--                                                      ^^^^^
-- Can include automatically with non-trivial comparison between actual
-- term and given partial element
