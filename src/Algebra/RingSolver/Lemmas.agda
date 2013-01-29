------------------------------------------------------------------------
-- The Agda standard library
--
-- Some boring lemmas used by the ring solver
------------------------------------------------------------------------

-- Note that these proofs use all "almost commutative ring" properties.

open import Algebra
open import Algebra.RingSolver.AlmostCommutativeRing

module Algebra.RingSolver.Lemmas
  {r₁ r₂ r₃}
  (coeff : RawRing r₁)
  (r : AlmostCommutativeRing r₂ r₃)
  (morphism : coeff -Raw-AlmostCommutative⟶ r)
  where

private
  module C = RawRing coeff
open AlmostCommutativeRing r
open import Algebra.Morphism
open _-Raw-AlmostCommutative⟶_ morphism
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Function
open import Data.Product

lemma₀ : ∀ a b c x →
         (a + b) * x + c ≈ a * x + (b * x + c)
lemma₀ a b c x = begin
  (a + b) * x + c      ≈⟨ proj₂ distrib _ _ _ ⟨ +-cong ⟩ refl ⟩
  (a * x + b * x) + c  ≈⟨ +-assoc _ _ _ ⟩
  a * x + (b * x + c)  ∎

lemma₁ : ∀ a b c d x →
         (a + b) * x + (c + d) ≈ (a * x + c) + (b * x + d)
lemma₁ a b c d x = begin
  (a + b) * x + (c + d)      ≈⟨ lemma₀ _ _ _ _ ⟩
  a * x + (b * x + (c + d))  ≈⟨ refl ⟨ +-cong ⟩ sym (+-assoc _ _ _) ⟩
  a * x + ((b * x + c) + d)  ≈⟨ refl ⟨ +-cong ⟩ (+-comm _ _ ⟨ +-cong ⟩ refl) ⟩
  a * x + ((c + b * x) + d)  ≈⟨ refl ⟨ +-cong ⟩ +-assoc _ _ _ ⟩
  a * x + (c + (b * x + d))  ≈⟨ sym $ +-assoc _ _ _ ⟩
  (a * x + c) + (b * x + d)  ∎

lemma₂ : ∀ a b c x → a * c * x + b * c ≈ (a * x + b) * c
lemma₂ a b c x = begin
  a * c * x + b * c  ≈⟨ lem ⟨ +-cong ⟩ refl ⟩
  a * x * c + b * c  ≈⟨ sym $ proj₂ distrib _ _ _ ⟩
  (a * x + b) * c    ∎
  where
  lem = begin
    a * c * x    ≈⟨ *-assoc _ _ _ ⟩
    a * (c * x)  ≈⟨ refl ⟨ *-cong ⟩ *-comm _ _ ⟩
    a * (x * c)  ≈⟨ sym $ *-assoc _ _ _ ⟩
    a * x * c    ∎

lemma₃ : ∀ a b c x → a * b * x + a * c ≈ a * (b * x + c)
lemma₃ a b c x = begin
  a * b * x + a * c    ≈⟨ *-assoc _ _ _ ⟨ +-cong ⟩ refl ⟩
  a * (b * x) + a * c  ≈⟨ sym $ proj₁ distrib _ _ _ ⟩
  a * (b * x + c)      ∎

lemma₄ : ∀ a b c d x →
         (a * c * x + (a * d + b * c)) * x + b * d ≈
         (a * x + b) * (c * x + d)
lemma₄ a b c d x = begin
  (a * c * x + (a * d + b * c)) * x + b * d              ≈⟨ proj₂ distrib _ _ _ ⟨ +-cong ⟩ refl ⟩
  (a * c * x * x + (a * d + b * c) * x) + b * d          ≈⟨ refl ⟨ +-cong ⟩ ((refl ⟨ +-cong ⟩ refl) ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ refl ⟩
  (a * c * x * x + (a * d + b * c) * x) + b * d          ≈⟨ +-assoc _ _ _  ⟩
  a * c * x * x + ((a * d + b * c) * x + b * d)          ≈⟨ lem₁ ⟨ +-cong ⟩ (lem₂ ⟨ +-cong ⟩ refl) ⟩
  a * x * (c * x) + (a * x * d + b * (c * x) + b * d)    ≈⟨ refl ⟨ +-cong ⟩ +-assoc _ _ _ ⟩
  a * x * (c * x) + (a * x * d + (b * (c * x) + b * d))  ≈⟨ sym $ +-assoc _ _ _ ⟩
  a * x * (c * x) + a * x * d + (b * (c * x) + b * d)    ≈⟨ sym $ proj₁ distrib _ _ _ ⟨ +-cong ⟩ proj₁ distrib _ _ _ ⟩
  a * x * (c * x + d) + b * (c * x + d)                  ≈⟨ sym $ proj₂ distrib _ _ _ ⟩
  (a * x + b) * (c * x + d)                              ∎
  where
  lem₁′ = begin
    a * c * x    ≈⟨ *-assoc _ _ _ ⟩
    a * (c * x)  ≈⟨ refl ⟨ *-cong ⟩ *-comm _ _ ⟩
    a * (x * c)  ≈⟨ sym $ *-assoc _ _ _ ⟩
    a * x * c    ∎

  lem₁ = begin
    a * c * x * x    ≈⟨ lem₁′ ⟨ *-cong ⟩ refl ⟩
    a * x * c * x    ≈⟨ *-assoc _ _ _ ⟩
    a * x * (c * x)  ∎

  lem₂ = begin
    (a * d + b * c) * x        ≈⟨ proj₂ distrib _ _ _ ⟩
    a * d * x + b * c * x      ≈⟨ *-assoc _ _ _ ⟨ +-cong ⟩ *-assoc _ _ _ ⟩
    a * (d * x) + b * (c * x)  ≈⟨ (refl ⟨ *-cong ⟩ *-comm _ _) ⟨ +-cong ⟩ refl ⟩
    a * (x * d) + b * (c * x)  ≈⟨ sym $ *-assoc _ _ _ ⟨ +-cong ⟩ refl ⟩
    a * x * d + b * (c * x)    ∎

lemma₅ : ∀ x → (0# * x + 1#) * x + 0# ≈ x
lemma₅ x = begin
  (0# * x + 1#) * x + 0#   ≈⟨ ((zeroˡ _ ⟨ +-cong ⟩ refl) ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ refl ⟩
  (0# + 1#) * x + 0#       ≈⟨ (proj₁ +-identity _ ⟨ *-cong ⟩ refl) ⟨ +-cong ⟩ refl ⟩
  1# * x + 0#              ≈⟨ proj₂ +-identity _ ⟩
  1# * x                   ≈⟨ proj₁ *-identity _ ⟩
  x                        ∎

lemma₆ : ∀ a x → 0# * x + a ≈ a
lemma₆ a x = begin
  0# * x + a    ≈⟨ zeroˡ _ ⟨ +-cong ⟩ refl ⟩
  0# + a        ≈⟨ proj₁ +-identity _ ⟩
  a             ∎

lemma₇ : ∀ x → - 1# * x ≈ - x
lemma₇ x = begin
  - 1# * x      ≈⟨ -‿*-distribˡ _ _ ⟩
  - (1# * x)    ≈⟨ -‿cong (proj₁ *-identity _) ⟩
  - x           ∎
