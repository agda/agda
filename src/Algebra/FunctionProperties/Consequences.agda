------------------------------------------------------------------------
-- The Agda standard library
--
-- Relations between properties of functions, such as associativity and
-- commutativity
------------------------------------------------------------------------

open import Relation.Binary using (Setoid)

module Algebra.FunctionProperties.Consequences
  {a ℓ} (S : Setoid a ℓ) where

open Setoid S
open import Algebra.FunctionProperties _≈_
open import Relation.Binary.EqReasoning S
open import Data.Sum using (inj₁; inj₂)

------------------------------------------------------------------------
-- Transposing identity elements

comm+idˡ⇒idʳ : ∀ {_•_} → Commutative _•_ →
              ∀ {e} → LeftIdentity e _•_ → RightIdentity e _•_
comm+idˡ⇒idʳ {_•_} comm {e} idˡ x = begin
  x • e ≈⟨ comm x e ⟩
  e • x ≈⟨ idˡ x ⟩
  x     ∎

comm+idʳ⇒idˡ : ∀ {_•_} → Commutative _•_ →
              ∀ {e} → RightIdentity e _•_ → LeftIdentity e _•_
comm+idʳ⇒idˡ {_•_} comm {e} idʳ x = begin
  e • x ≈⟨ comm e x ⟩
  x • e ≈⟨ idʳ x ⟩
  x     ∎

------------------------------------------------------------------------
-- Transposing zero elements

comm+zeˡ⇒zeʳ : ∀ {_•_} → Commutative _•_ →
              ∀ {e} → LeftZero e _•_ → RightZero e _•_
comm+zeˡ⇒zeʳ {_•_} comm {e} zeˡ x = begin
  x • e ≈⟨ comm x e ⟩
  e • x ≈⟨ zeˡ x ⟩
  e     ∎

comm+zeʳ⇒zeˡ : ∀ {_•_} → Commutative _•_ →
              ∀ {e} → RightZero e _•_ → LeftZero e _•_
comm+zeʳ⇒zeˡ {_•_} comm {e} zeʳ x = begin
  e • x ≈⟨ comm e x ⟩
  x • e ≈⟨ zeʳ x ⟩
  e     ∎

------------------------------------------------------------------------
-- Transposing inverse elements

comm+invˡ⇒invʳ : ∀ {e _⁻¹ _•_} → Commutative _•_ →
                LeftInverse e _⁻¹ _•_ → RightInverse e _⁻¹ _•_
comm+invˡ⇒invʳ {e} {_⁻¹} {_•_} comm invˡ x = begin
  x • (x ⁻¹) ≈⟨ comm x (x ⁻¹) ⟩
  (x ⁻¹) • x ≈⟨ invˡ x ⟩
  e          ∎

comm+invʳ⇒invˡ : ∀ {e _⁻¹ _•_} → Commutative _•_ →
                RightInverse e _⁻¹ _•_ → LeftInverse e _⁻¹ _•_
comm+invʳ⇒invˡ {e} {_⁻¹} {_•_} comm invʳ x = begin
  (x ⁻¹) • x ≈⟨ comm (x ⁻¹) x ⟩
  x • (x ⁻¹) ≈⟨ invʳ x ⟩
  e          ∎

------------------------------------------------------------------------
-- Transposing distributivity

comm+distrˡ⇒distrʳ : ∀ {_•_ _◦_} → Congruent₂ _◦_ → Commutative _•_ →
                   _•_ DistributesOverˡ _◦_ → _•_ DistributesOverʳ _◦_
comm+distrˡ⇒distrʳ {_•_} {_◦_} cong comm distrˡ x y z = begin
  (y ◦ z) • x       ≈⟨ comm (y ◦ z) x ⟩
  x • (y ◦ z)       ≈⟨ distrˡ x y z ⟩
  (x • y) ◦ (x • z) ≈⟨ cong (comm x y) (comm x z) ⟩
  (y • x) ◦ (z • x) ∎

comm+distrʳ⇒distrˡ : ∀ {_•_ _◦_} → Congruent₂ _◦_ → Commutative _•_ →
                   _•_ DistributesOverʳ _◦_ → _•_ DistributesOverˡ _◦_
comm+distrʳ⇒distrˡ {_•_} {_◦_} cong comm distrˡ x y z = begin
  x • (y ◦ z)       ≈⟨ comm x (y ◦ z) ⟩
  (y ◦ z) • x       ≈⟨ distrˡ x y z ⟩
  (y • x) ◦ (z • x) ≈⟨ cong (comm y x) (comm z x) ⟩
  (x • y) ◦ (x • z) ∎

------------------------------------------------------------------------
-- Selectivity implies idempotence

sel⇒idem : ∀ {_•_} → Selective _•_ → Idempotent _•_
sel⇒idem sel x with sel x x
... | inj₁ x•x≈x = x•x≈x
... | inj₂ x•x≈x = x•x≈x
