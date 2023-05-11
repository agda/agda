{-# OPTIONS --cubical #-}

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Glue
open import Agda.Builtin.Cubical.Id
open import Agda.Builtin.Sigma
open import Agda.Primitive.Cubical
  renaming
    ( primIMax to _∨_
    ; primIMin to _∧_
    ; primINeg to ~_
    ; primComp to comp
    ; primHComp to primHComp
    ; primTransp to transp
    ; itIsOne to 1=1
    )

hcomp
  : ∀ {ℓ} {A : Type ℓ} (φ : I)
  → (u : (i : I) → Partial (φ ∨ ~ i) A)
  → A
hcomp φ u = primHComp (λ { j (φ = i1) → u j 1=1 }) (u i0 1=1)

hfill : ∀ {ℓ} {A : Type ℓ} (φ : I) → I
      → (u : (i : I) → Partial (φ ∨ ~ i) A)
      → A
hfill φ i u = hcomp (φ ∨ ~ i) λ where
  j (φ = i1) → {!   !}
  j (i = i0) → u i0 1=1
  j (j = i0) → u i0 1=1
