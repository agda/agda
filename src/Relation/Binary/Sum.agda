------------------------------------------------------------------------
-- The Agda standard library
--
-- Sums of binary relations
--
-- This module is DEPRECATED. Please use the Data.Sum.Relation modules
-- directly.
------------------------------------------------------------------------

module Relation.Binary.Sum where

open import Data.Sum.Relation.Core public

open import Data.Sum.Relation.Pointwise public
  using ()
  renaming
  ( Pointwise          to _⊎-Rel_
  ; ⊎-symmetric        to _⊎-symmetric_
  ; ⊎-substitutive     to _⊎-substitutive_
  ; ⊎-isEquivalence    to _⊎-isEquivalence_
  ; ⊎-isDecEquivalence to _⊎-isDecEquivalence_
  ; ⊎-setoid           to _⊎-setoid_
  ; ⊎-decSetoid        to _⊎-decSetoid_
  ; Pointwise-≡↔≡      to ⊎-Rel↔≡
  )

open import Data.Sum.Relation.LeftOrder public
  using ()
  renaming
  ( ⊎-<-total              to _⊎-<-total_
  ; ⊎-<-trichotomous       to _⊎-<-trichotomous_
  ; ⊎-<-isTotalOrder       to _⊎-<-isTotalOrder_
  ; ⊎-<-isDecTotalOrder    to _⊎-<-isDecTotalOrder_
  ; ⊎-<-isStrictTotalOrder to _⊎-<-isStrictTotalOrder_
  ; ⊎-<-poset              to _⊎-<-poset_
  ; ⊎-<-strictPartialOrder to _⊎-<-strictPartialOrder_
  ; ⊎-<-totalOrder         to _⊎-<-totalOrder_
  ; ⊎-<-decTotalOrder      to _⊎-<-decTotalOrder_
  ; ⊎-<-strictTotalOrder   to _⊎-<-strictTotalOrder_
  )
