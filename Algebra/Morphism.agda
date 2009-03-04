------------------------------------------------------------------------
-- Morphisms between algebraic structures
------------------------------------------------------------------------

module Algebra.Morphism where

open import Relation.Binary
open import Algebra
open import Algebra.FunctionProperties
open import Data.Function

------------------------------------------------------------------------
-- Basic definitions

module Definitions (from : Set) (to : Setoid) where
  open Setoid to renaming (carrier to to-carrier)

  Morphism : Set
  Morphism = from → to-carrier

  Homomorphic₀ : Morphism → from → to-carrier → Set
  Homomorphic₀ ⟦_⟧ ∙ ∘ = ⟦ ∙ ⟧ ≈ ∘

  Homomorphic₁ : Morphism → Fun₁ from → Op₁ to → Set
  Homomorphic₁ ⟦_⟧ ∙_ ∘_ = ∀ x → ⟦ ∙ x ⟧ ≈ ∘ ⟦ x ⟧

  Homomorphic₂ : Morphism → Fun₂ from → Op₂ to → Set
  Homomorphic₂ ⟦_⟧ _∙_ _∘_ =
    ∀ x y → ⟦ x ∙ y ⟧ ≈ (⟦ x ⟧ ∘ ⟦ y ⟧)

------------------------------------------------------------------------
-- Some specific morphisms

-- Other morphisms could of course be defined.

record _-RawRing⟶_ (from to : RawRing) : Set where
  open RawRing
  open Definitions (carrier from) (setoid to)
  field
    ⟦_⟧    : Morphism
    +-homo : Homomorphic₂ ⟦_⟧ (_+_ from) (_+_ to)
    *-homo : Homomorphic₂ ⟦_⟧ (_*_ from) (_*_ to)
    -‿homo : Homomorphic₁ ⟦_⟧ (-_  from) (-_  to)
    0-homo : Homomorphic₀ ⟦_⟧ (0#  from) (0#  to)
    1-homo : Homomorphic₀ ⟦_⟧ (1#  from) (1#  to)

_-Ring⟶_ : Ring → Ring → Set
from -Ring⟶ to = rawRing from -RawRing⟶ rawRing to
  where open Ring
