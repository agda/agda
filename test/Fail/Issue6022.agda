-- Andreas, 2022-09-30, issue #6022, test by Amelia

-- Dead-code elimination removed private primitives
-- used in cubical stuff, leading to a crash.

{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical renaming (primTransp to transp)

open import Issue6022.Cubical

module _ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) where

  q : Id x y
  q = transp (λ i → Id x (p i)) i0 refl

  q' : Id x y
  q' = transp (λ i → Id x (p i)) i0 refl

  test : q ≡ q'
  test i = {!!}

-- WAS: crash due to unbound name
-- Expected error: Failed to solve constraints.
