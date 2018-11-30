
module _ where

open import Agda.Primitive

-- Named implicit parameters

data D₁ {a b} (A : Set a) (B : Set b) : Set (a ⊔ lsuc b)
data D₁ {b = c} X Y where
  mkD₁ : Set c → D₁ X Y

-- Trailing implicit parameters

data D₂ {a} : Set a
data D₂ where
  tt : D₂
