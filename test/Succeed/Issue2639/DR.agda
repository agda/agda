module Issue2639.DR (Z : Set) where

open import Agda.Builtin.Size

mutual

  data D (i : Size) : Set where
    a : D i
    b : R i → D i

  record R (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → D j
