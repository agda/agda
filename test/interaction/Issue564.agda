module Issue564 where

postulate
  Level : Set
  zero  : Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}

postulate
  A : Level → Set

module M ℓ where
  postulate a : A ℓ

postulate
  P : A zero → Set

open M zero

p : P a
p = {!!}
