-- Andreas, 2026-10-20, issue #8853, reported by dancewithheart
-- Internal error in ReconstructParameters on path application (IApply).

{-# OPTIONS --cubical --safe #-}

open import Agda.Builtin.Reflection
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.List using ([])
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Cubical.Path using (_≡_)

f : (p : tt ≡ tt) → tt ≡ tt
f p i = p i

macro
  crash : Term → TC ⊤
  crash h =
    bindTC (withReconstructed true (getDefinition (quote f)))
      (λ _ → unify h (con (quote tt) []))

test : ⊤
test = crash

-- Used to crash with internal error in ReconstructParameters.
