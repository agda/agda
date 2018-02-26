------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable equality over lists using propositional equality
------------------------------------------------------------------------

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Data.List.Relation.Equality.DecPropositional
  {a} {A : Set a} (_≟_ : Decidable {A = A} _≡_) where

import Data.List.Relation.Equality.Propositional as PropositionalEq
import Data.List.Relation.Equality.DecSetoid as DecSetoidEq

------------------------------------------------------------------------
-- Publically re-export everything from decSetoid and propositional
-- equality

open PropositionalEq public
open DecSetoidEq (decSetoid _≟_) public
  using (_≋?_; ≋-isDecEquivalence; ≋-decSetoid)
