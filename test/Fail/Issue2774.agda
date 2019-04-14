
open import Agda.Builtin.Size

data D : Size → Set where

postulate
  f : (i : Size) → D i

data P : (i : Size) → D i → Set where
  c : (i j : Size) → P (i ⊔ˢ j) (f _)
