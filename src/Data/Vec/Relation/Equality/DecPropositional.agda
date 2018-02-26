------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable vector equality over propositional equality
------------------------------------------------------------------------

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Data.Vec.Relation.Equality.DecPropositional
  {a} {A : Set a} (_≟_ : Decidable {A = A} _≡_) where

import Data.Vec.Relation.Equality.Propositional as PEq
import Data.Vec.Relation.Equality.DecSetoid as DSEq

------------------------------------------------------------------------
-- Publically re-export everything from decSetoid and propositional
-- equality

open PEq public
open DSEq (decSetoid _≟_) public
  using (_≋?_; ≋-isDecEquivalence; ≋-decSetoid)
