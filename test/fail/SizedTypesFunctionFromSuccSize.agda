{-# OPTIONS --sized-types --injective-type-constructors #-}

module SizedTypesFunctionFromSuccSize where

postulate
  Size : Set
  _^   : Size -> Size
  ∞    : Size

{-# BUILTIN SIZE Size  #-}
{-# BUILTIN SIZESUC _^ #-}
{-# BUILTIN SIZEINF ∞  #-}

data Nat : {size : Size} -> Set where
  zero : {size : Size} -> Nat {size ^}
  suc  : {size : Size} -> Nat {size} -> Nat {size ^}

bad : {i : Size} -> Nat {i ^} -> Set
bad (zero) = bad zero
bad (suc x) = Nat

