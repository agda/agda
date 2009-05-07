------------------------------------------------------------------------
-- Some boring lemmas used by the ring solver
------------------------------------------------------------------------

-- Note that these proofs use all "almost commutative ring" properties
-- except for zero and -‿pres-≈.

open import Algebra
open import Algebra.RingSolver.AlmostCommutativeRing

module Algebra.RingSolver.Lemmas
  (coeff : RawRing)
  (r : AlmostCommutativeRing)
  (morphism : coeff -Raw-AlmostCommutative⟶ r)
  where

private
  module C = RawRing coeff
open AlmostCommutativeRing r
open import Algebra.Morphism
open _-RawRing⟶_ morphism
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Data.Function
open import Data.Product

lemma₀ : ∀ x → x + ⟦ C.0# ⟧ ≈ x
lemma₀ x = begin
  x + ⟦ C.0# ⟧  ≈⟨ refl ⟨ +-pres-≈ ⟩ 0-homo ⟩
  x + 0#        ≈⟨ proj₂ +-identity _ ⟩
  x             ∎

lemma₁ : ∀ a b c d x →
         (a + b) * x + (c + d) ≈ (a * x + c) + (b * x + d)
lemma₁ a b c d x = begin
  (a + b) * x + (c + d)      ≈⟨ proj₂ distrib _ _ _ ⟨ +-pres-≈ ⟩ refl ⟩
  (a * x + b * x) + (c + d)  ≈⟨ +-assoc _ _ _ ⟩
  a * x + (b * x + (c + d))  ≈⟨ refl ⟨ +-pres-≈ ⟩ sym (+-assoc _ _ _) ⟩
  a * x + ((b * x + c) + d)  ≈⟨ refl ⟨ +-pres-≈ ⟩ (+-comm _ _ ⟨ +-pres-≈ ⟩ refl) ⟩
  a * x + ((c + b * x) + d)  ≈⟨ refl ⟨ +-pres-≈ ⟩ +-assoc _ _ _ ⟩
  a * x + (c + (b * x + d))  ≈⟨ sym $ +-assoc _ _ _ ⟩
  (a * x + c) + (b * x + d)  ∎

lemma₂ : ∀ x y z → x + (y + z) ≈ y + (x + z)
lemma₂ x y z = begin
  x + (y + z)  ≈⟨ sym $ +-assoc _ _ _ ⟩
  (x + y) + z  ≈⟨ +-comm _ _ ⟨ +-pres-≈ ⟩ refl ⟩
  (y + x) + z  ≈⟨ +-assoc _ _ _ ⟩
  y + (x + z)  ∎

lemma₃ : ∀ a b c x → a * c * x + b * c ≈ (a * x + b) * c
lemma₃ a b c x = begin
  a * c * x + b * c  ≈⟨ lem ⟨ +-pres-≈ ⟩ refl ⟩
  a * x * c + b * c  ≈⟨ sym $ proj₂ distrib _ _ _ ⟩
  (a * x + b) * c    ∎
  where
  lem = begin
    a * c * x    ≈⟨ *-assoc _ _ _ ⟩
    a * (c * x)  ≈⟨ refl ⟨ *-pres-≈ ⟩ *-comm _ _ ⟩
    a * (x * c)  ≈⟨ sym $ *-assoc _ _ _ ⟩
    a * x * c    ∎

lemma₄ : ∀ a b c x → a * b * x + a * c ≈ a * (b * x + c)
lemma₄ a b c x = begin
  a * b * x + a * c    ≈⟨ *-assoc _ _ _ ⟨ +-pres-≈ ⟩ refl ⟩
  a * (b * x) + a * c  ≈⟨ sym $ proj₁ distrib _ _ _ ⟩
  a * (b * x + c)      ∎

lemma₅ : ∀ a b c d x →
         a * c * x * x + ((a * d + b * c) * x + b * d) ≈
         (a * x + b) * (c * x + d)
lemma₅ a b c d x = begin
  a * c * x * x +
  ((a * d + b * c) * x + b * d)          ≈⟨ lem₁ ⟨ +-pres-≈ ⟩
                                            (lem₂ ⟨ +-pres-≈ ⟩ refl) ⟩
  a * x * (c * x) +
  (a * x * d + b * (c * x) + b * d)      ≈⟨ refl ⟨ +-pres-≈ ⟩ +-assoc _ _ _ ⟩
  a * x * (c * x) +
  (a * x * d + (b * (c * x) + b * d))    ≈⟨ sym $ +-assoc _ _ _ ⟩
  a * x * (c * x) + a * x * d +
  (b * (c * x) + b * d)                  ≈⟨ sym $ proj₁ distrib _ _ _
                                                  ⟨ +-pres-≈ ⟩
                                                proj₁ distrib _ _ _ ⟩
  a * x * (c * x + d) + b * (c * x + d)  ≈⟨ sym $ proj₂ distrib _ _ _ ⟩
  (a * x + b) * (c * x + d)              ∎
  where
  lem₁' = begin
    a * c * x    ≈⟨ *-assoc _ _ _ ⟩
    a * (c * x)  ≈⟨ refl ⟨ *-pres-≈ ⟩ *-comm _ _ ⟩
    a * (x * c)  ≈⟨ sym $ *-assoc _ _ _ ⟩
    a * x * c    ∎

  lem₁ = begin
    a * c * x * x    ≈⟨ lem₁' ⟨ *-pres-≈ ⟩ refl ⟩
    a * x * c * x    ≈⟨ *-assoc _ _ _ ⟩
    a * x * (c * x)  ∎

  lem₂ = begin
    (a * d + b * c) * x        ≈⟨ proj₂ distrib _ _ _ ⟩
    a * d * x + b * c * x      ≈⟨ *-assoc _ _ _ ⟨ +-pres-≈ ⟩ *-assoc _ _ _ ⟩
    a * (d * x) + b * (c * x)  ≈⟨ (refl ⟨ *-pres-≈ ⟩ *-comm _ _)
                                    ⟨ +-pres-≈ ⟩ refl ⟩
    a * (x * d) + b * (c * x)  ≈⟨ sym $ *-assoc _ _ _ ⟨ +-pres-≈ ⟩ refl ⟩
    a * x * d + b * (c * x)    ∎

lemma₆ : ∀ a b x → - a * x + - b ≈ - (a * x + b)
lemma₆ a b x = begin
  - a * x + - b    ≈⟨ -‿*-distribˡ _ _ ⟨ +-pres-≈ ⟩ refl ⟩
  - (a * x) + - b  ≈⟨ -‿+-comm _ _ ⟩
  - (a * x + b)    ∎

lemma₇ : ∀ x → ⟦ C.1# ⟧ * x + ⟦ C.0# ⟧ ≈ x
lemma₇ x = begin
  ⟦ C.1# ⟧ * x + ⟦ C.0# ⟧  ≈⟨ (1-homo ⟨ *-pres-≈ ⟩ refl) ⟨ +-pres-≈ ⟩ 0-homo ⟩
  1# * x + 0#              ≈⟨ proj₂ +-identity _ ⟩
  1# * x                   ≈⟨ proj₁ *-identity _ ⟩
  x                        ∎
