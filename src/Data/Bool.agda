------------------------------------------------------------------------
-- The Agda standard library
--
-- Booleans
------------------------------------------------------------------------

module Data.Bool where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

------------------------------------------------------------------------
-- The boolean type and some operations

open import Data.Bool.Base public

------------------------------------------------------------------------
-- Some properties

decSetoid : DecSetoid _ _
decSetoid = PropEq.decSetoid _≟_
