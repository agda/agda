------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable equality over lists parameterised by some setoid
------------------------------------------------------------------------

open import Relation.Binary

module Data.List.Relation.Equality.DecSetoid
  {a ℓ} (DS : DecSetoid a ℓ) where

import Data.List.Relation.Equality.Setoid as SetoidEquality
import Data.List.Relation.Pointwise as PW
open import Relation.Binary using (Decidable)
open DecSetoid DS

------------------------------------------------------------------------
-- Make all definitions from setoid equality available

open SetoidEquality setoid public

------------------------------------------------------------------------
-- Additional properties

infix 4 _≋?_

_≋?_ : Decidable _≋_
_≋?_ = PW.decidable _≟_

≋-isDecEquivalence : IsDecEquivalence _≋_
≋-isDecEquivalence = PW.isDecEquivalence isDecEquivalence

≋-decSetoid : DecSetoid a ℓ
≋-decSetoid = PW.decSetoid DS
