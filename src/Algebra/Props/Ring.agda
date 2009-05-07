------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Props.Ring (r : Ring) where

open Ring r
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Data.Function
open import Data.Product

-‿*-distribˡ : ∀ x y → - x * y ≈ - (x * y)
-‿*-distribˡ x y = begin
  - x * y                        ≈⟨ sym $ proj₂ +-identity _ ⟩
  - x * y + 0#                   ≈⟨ refl ⟨ +-pres-≈ ⟩ sym (proj₂ -‿inverse _) ⟩
  - x * y + (x * y + - (x * y))  ≈⟨ sym $ +-assoc _ _ _  ⟩
  - x * y + x * y + - (x * y)    ≈⟨ sym (proj₂ distrib _ _ _) ⟨ +-pres-≈ ⟩ refl ⟩
  (- x + x) * y + - (x * y)      ≈⟨ (proj₁ -‿inverse _ ⟨ *-pres-≈ ⟩ refl)
                                      ⟨ +-pres-≈ ⟩
                                    refl ⟩
  0# * y + - (x * y)             ≈⟨ proj₁ zero _ ⟨ +-pres-≈ ⟩ refl ⟩
  0# + - (x * y)                 ≈⟨ proj₁ +-identity _ ⟩
  - (x * y)                      ∎

-‿*-distribʳ : ∀ x y → x * - y ≈ - (x * y)
-‿*-distribʳ x y = begin
  x * - y                        ≈⟨ sym $ proj₁ +-identity _ ⟩
  0# + x * - y                   ≈⟨ sym (proj₁ -‿inverse _) ⟨ +-pres-≈ ⟩ refl ⟩
  - (x * y) + x * y + x * - y    ≈⟨ +-assoc _ _ _  ⟩
  - (x * y) + (x * y + x * - y)  ≈⟨ refl ⟨ +-pres-≈ ⟩ sym (proj₁ distrib _ _ _)  ⟩
  - (x * y) + x * (y + - y)      ≈⟨ refl ⟨ +-pres-≈ ⟩ (refl ⟨ *-pres-≈ ⟩ proj₂ -‿inverse _) ⟩
  - (x * y) + x * 0#             ≈⟨ refl ⟨ +-pres-≈ ⟩ proj₂ zero _ ⟩
  - (x * y) + 0#                 ≈⟨ proj₂ +-identity _ ⟩
  - (x * y)                      ∎
