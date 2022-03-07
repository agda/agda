-- Andreas, bug found 2011-12-31

{-# OPTIONS --irrelevant-projections #-}

module Issue543 where

open import Common.Equality

data   ⊥ : Set where
record ⊤ : Set where
  constructor tt

data Bool : Set where
  true false : Bool

T : Bool → Set
T true  = ⊤
T false = ⊥

record Squash {ℓ}(A : Set ℓ) : Set ℓ where
  constructor squash
  field
    .unsquash : A
open Squash

-- ok:
sqT≡sqF : squash true ≡ squash false
sqT≡sqF = refl

-- this should not be provable!!
.irrT≡F : true ≡ false
irrT≡F = subst (λ s → unsquash (squash true) ≡ unsquash s) sqT≡sqF refl

-- the rest is easy
T≠F : true ≡ false → ⊥
T≠F p = subst T p tt

.irr⊥ : ⊥
irr⊥ = T≠F irrT≡F

rel⊥ : .⊥ → ⊥
rel⊥ ()

absurd : ⊥
absurd = rel⊥ irr⊥
