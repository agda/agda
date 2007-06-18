------------------------------------------------------------------------
-- Definitions of morphisms
------------------------------------------------------------------------

open import Prelude.BinaryRelation

module Prelude.Algebra.Morphism (from to : Setoid) where

import Prelude.Algebra as Alg
private
  module F = Setoid from
  module F = Alg from
  module T = Setoid to
  module T = Alg to
  open module TE = Setoid to using (_≈_)

------------------------------------------------------------------------
-- Basic definitions

Morphism : Set
Morphism = F.carrier -> T.carrier

Homomorphic₀ : Morphism -> F.carrier -> T.carrier -> Set
Homomorphic₀ ⟦_⟧ • •' = ⟦ • ⟧ ≈ •'

Homomorphic₁ : Morphism -> F.Op₁ -> T.Op₁ -> Set
Homomorphic₁ ⟦_⟧ •_ •'_ = forall x -> ⟦ • x ⟧ ≈ •' ⟦ x ⟧

Homomorphic₂ : Morphism -> F.Op₂ -> T.Op₂ -> Set
Homomorphic₂ ⟦_⟧ _•_ _•'_ =
  forall x y -> ⟦ x • y ⟧ ≈ (⟦ x ⟧ •' ⟦ y ⟧)

------------------------------------------------------------------------
-- Some specific morphisms

record RingHomomorphism
  (F+ F* : F.Op₂) (F- : F.Op₁) (F0# F1# : F.carrier)
  (T+ T* : T.Op₂) (T- : T.Op₁) (T0# T1# : T.carrier)
  : Set where
  ⟦_⟧    : Morphism
  +-homo : Homomorphic₂ ⟦_⟧ F+ T+
  *-homo : Homomorphic₂ ⟦_⟧ F* T*
  ¬-homo : Homomorphic₁ ⟦_⟧ F- T-
  0-homo : Homomorphic₀ ⟦_⟧ F0# T0#
  1-homo : Homomorphic₀ ⟦_⟧ F1# T1#
