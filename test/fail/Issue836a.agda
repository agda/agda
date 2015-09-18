
module _ where

module N (_ : Set₁) where

  data D : Set₁ where
    c : Set → D

open N Set using (D) renaming (module D to MD)

open import Common.Equality

-- No longer two ways to qualify
twoWaysToQualify : D.c ≡ MD.c
twoWaysToQualify = refl

