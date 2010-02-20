------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Algebra

module Algebra.Props.Ring {r₁ r₂} (R : Ring r₁ r₂) where

open Ring R
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Function
open import Data.Product

-‿*-distribˡ : ∀ x y → - x * y ≈ - (x * y)
-‿*-distribˡ x y = begin
  - x * y                        ≈⟨ sym $ proj₂ +-identity _ ⟩
  - x * y + 0#                   ≈⟨ refl ⟨ +-cong ⟩ sym (proj₂ -‿inverse _) ⟩
  - x * y + (x * y + - (x * y))  ≈⟨ sym $ +-assoc _ _ _  ⟩
  - x * y + x * y + - (x * y)    ≈⟨ sym (proj₂ distrib _ _ _) ⟨ +-cong ⟩ refl ⟩
  (- x + x) * y + - (x * y)      ≈⟨ (proj₁ -‿inverse _ ⟨ *-cong ⟩ refl)
                                      ⟨ +-cong ⟩
                                    refl ⟩
  0# * y + - (x * y)             ≈⟨ proj₁ zero _ ⟨ +-cong ⟩ refl ⟩
  0# + - (x * y)                 ≈⟨ proj₁ +-identity _ ⟩
  - (x * y)                      ∎

-‿*-distribʳ : ∀ x y → x * - y ≈ - (x * y)
-‿*-distribʳ x y = begin
  x * - y                        ≈⟨ sym $ proj₁ +-identity _ ⟩
  0# + x * - y                   ≈⟨ sym (proj₁ -‿inverse _) ⟨ +-cong ⟩ refl ⟩
  - (x * y) + x * y + x * - y    ≈⟨ +-assoc _ _ _  ⟩
  - (x * y) + (x * y + x * - y)  ≈⟨ refl ⟨ +-cong ⟩ sym (proj₁ distrib _ _ _)  ⟩
  - (x * y) + x * (y + - y)      ≈⟨ refl ⟨ +-cong ⟩ (refl ⟨ *-cong ⟩ proj₂ -‿inverse _) ⟩
  - (x * y) + x * 0#             ≈⟨ refl ⟨ +-cong ⟩ proj₂ zero _ ⟩
  - (x * y) + 0#                 ≈⟨ proj₂ +-identity _ ⟩
  - (x * y)                      ∎
