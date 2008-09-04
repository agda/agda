{-# OPTIONS --sized-types --show-implicit #-}

module WrongSizeAssignment where

postulate
  Size : Set
  _^   : Size -> Size
  ∞    : Size

{-# BUILTIN SIZE Size  #-}
{-# BUILTIN SIZESUC _^ #-}
{-# BUILTIN SIZEINF ∞  #-}

data Empty : Set where

data N : {_ : Size} -> Set where
  zero : N {∞}
  suc  : forall {i} -> N {i ^} -> N {i}

lift : forall {i} -> N {i} -> N {i ^}
lift zero    = zero
lift (suc x) = suc (lift x)

f : forall {i} -> N {i ^} -> Empty
f x = f (suc (lift x))
