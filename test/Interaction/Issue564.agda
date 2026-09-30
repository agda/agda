module Issue564 where

open import Agda.Primitive using (Level) renaming (lzero to zero)

postulate
  A : Level → Set

module M ℓ where
  postulate a : A ℓ

postulate
  P : A zero → Set

open M zero

p : P a
p = {!!}
