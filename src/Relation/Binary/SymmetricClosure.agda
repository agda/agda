------------------------------------------------------------------------
-- The Agda standard library
--
-- Symmetric closures of binary relations
------------------------------------------------------------------------

module Relation.Binary.SymmetricClosure where

open import Data.Sum as Sum using (_⊎_)
open import Function using (id)
open import Relation.Binary

open Sum public using () renaming (inj₁ to fwd; inj₂ to bwd)

-- The symmetric closure of a relation.

SymClosure : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Rel A ℓ
SymClosure _∼_ a b = a ∼ b ⊎ b ∼ a

module _ {a ℓ} {A : Set a} where

  -- Symmetric closures are symmetric.

  symmetric : (_∼_ : Rel A ℓ) → Symmetric (SymClosure _∼_)
  symmetric _ (fwd a∼b) = bwd a∼b
  symmetric _ (bwd b∼a) = fwd b∼a

  -- A generalised variant of map which allows the index type to change.

  gmap : ∀ {b ℓ₂} {B : Set b} {P : Rel A ℓ} {Q : Rel B ℓ₂} →
         (f : A → B) → P =[ f ]⇒ Q → SymClosure P =[ f ]⇒ SymClosure Q
  gmap _ g = Sum.map g g

  map : ∀ {ℓ₂} {P : Rel A ℓ} {Q : Rel A ℓ₂} →
        P ⇒ Q → SymClosure P ⇒ SymClosure Q
  map = gmap id
