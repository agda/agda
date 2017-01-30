------------------------------------------------------------------------
-- The Agda standard library
--
-- Equivalence closures of binary relations
------------------------------------------------------------------------

module Relation.Binary.EquivalenceClosure where

open import Data.Star as Star using (Star; ε; _◅◅_; reverse)
open import Function using (flip; id; _∘_)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.SymmetricClosure as SC using (SymClosure)

-- The reflexive, transitive and symmetric closure of a binary
-- relation (aka the equivalence closure).

EqClosure : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Rel A (a ⊔ ℓ)
EqClosure _∼_ = Star (SymClosure _∼_)

module _ {a ℓ} {A : Set a} where

  -- Equivalence closures are equivalences.

  reflexive : (_∼_ : Rel A ℓ) → Reflexive (EqClosure _∼_)
  reflexive _∼_ = ε

  transitive : (_∼_ : Rel A ℓ) → Transitive (EqClosure _∼_)
  transitive _∼_ = _◅◅_

  symmetric : (_∼_ : Rel A ℓ) → Symmetric (EqClosure _∼_)
  symmetric _∼_ = reverse (SC.symmetric _∼_)

  isEquivalence : (_∼_ : Rel A ℓ) → IsEquivalence (EqClosure _∼_)
  isEquivalence _∼_ = record
    { refl  = reflexive  _∼_
    ; sym   = symmetric  _∼_
    ; trans = transitive _∼_
    }

  -- The setoid associated with an equivalence closure.

  setoid : Rel A ℓ → Setoid a (a ⊔ ℓ)
  setoid _∼_ = record
    { _≈_           = EqClosure _∼_
    ; isEquivalence = isEquivalence _∼_
    }

  -- A generalised variant of map which allows the index type to change.

  gmap : ∀ {b ℓ₂} {B : Set b} {P : Rel A ℓ} {Q : Rel B ℓ₂} →
         (f : A → B) → P =[ f ]⇒ Q → EqClosure P =[ f ]⇒ EqClosure Q
  gmap {Q = Q} f = Star.gmap f ∘ SC.gmap {Q = Q} f

  map : ∀ {ℓ₂} {P : Rel A ℓ} {Q : Rel A ℓ₂} →
        P ⇒ Q → EqClosure P ⇒ EqClosure Q
  map = gmap id
