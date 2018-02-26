------------------------------------------------------------------------
-- The Agda standard library
--
-- Equality over lists parameterised by some setoid
------------------------------------------------------------------------

open import Relation.Binary using (Setoid)

module Data.List.Relation.Equality.Setoid {a ℓ} (S : Setoid a ℓ) where

open import Data.List.Base using (List)
open import Level
open import Relation.Binary renaming (Rel to Rel₂)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Data.List.Relation.Pointwise as PW using (Pointwise)

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definition of equality

infix 4 _≋_

_≋_ : Rel₂ (List A) ℓ
_≋_ = Pointwise _≈_

open Pointwise public using ([]; _∷_)

------------------------------------------------------------------------
-- Relational properties

≋-refl : Reflexive _≋_
≋-refl = PW.refl refl

≋-reflexive : _≡_ ⇒ _≋_
≋-reflexive P.refl = ≋-refl

≋-sym : Symmetric _≋_
≋-sym = PW.symmetric sym

≋-trans : Transitive _≋_
≋-trans = PW.transitive trans

≋-isEquivalence : IsEquivalence _≋_
≋-isEquivalence = PW.isEquivalence isEquivalence

≋-setoid : Setoid _ _
≋-setoid = PW.setoid S

------------------------------------------------------------------------
-- Operations

open PW public using
  ( tabulate⁺
  ; tabulate⁻
  ; ++⁺
  ; concat⁺
  )
