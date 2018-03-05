------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable semi-heterogeneous vector equality over setoids
------------------------------------------------------------------------

open import Relation.Binary

module Data.Vec.Relation.Equality.DecSetoid
  {a ℓ} (DS : DecSetoid a ℓ) where

open import Data.Nat using (ℕ)
import Data.Vec.Relation.Equality.Setoid as Equality
import Data.Vec.Relation.Pointwise.Inductive as PW
open import Level using (_⊔_)
open import Relation.Binary using (Decidable)

open DecSetoid DS

------------------------------------------------------------------------
-- Make all definitions from equality available

open Equality setoid public

------------------------------------------------------------------------
-- Additional properties

infix 4 _≋?_

_≋?_ : ∀ {m n} → Decidable (_≋_ {m} {n})
_≋?_ = PW.decidable _≟_

≋-isDecEquivalence : ∀ n → IsDecEquivalence (_≋_ {n})
≋-isDecEquivalence = PW.isDecEquivalence isDecEquivalence

≋-decSetoid : ℕ → DecSetoid a (a ⊔ ℓ)
≋-decSetoid = PW.decSetoid DS
