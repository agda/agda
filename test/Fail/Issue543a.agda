-- Andreas, bug found 2011-12-31

{-# OPTIONS --irrelevant-projections #-}

module Issue543a where

open import Common.Equality

data   ⊥ : Set where
record ⊤ : Set where
  constructor tt

data Bool : Set where
  true false : Bool

record Squash (A : Set) : Set where
  constructor squash
  field
    .unsquash : A
open Squash

-- ok:
sqT≡sqF : squash true ≡ squash false
sqT≡sqF = refl

record Inhabited : Set1 where
  constructor inhabited
  field
    Type : Set
    elem : Type
open Inhabited

.bad1 : Inhabited
bad1 = inhabited (true ≡ unsquash (squash true)) refl

.bad2 : Inhabited
bad2 = inhabited (unsquash (squash false) ≡ false) refl

infixl 2 _∘_
_∘_ = trans

-- this should not be provable!!
.irrT≡F : true ≡ false
irrT≡F = elem bad1 ∘ cong unsquash sqT≡sqF ∘ elem bad2

-- the rest is easy

T : Bool → Set
T true  = ⊤
T false = ⊥

T≠F : true ≡ false → ⊥
T≠F p = subst T p tt

.irr⊥ : ⊥
irr⊥ = T≠F irrT≡F

rel⊥ : .⊥ → ⊥
rel⊥ ()

absurd : ⊥
absurd = rel⊥ irr⊥
