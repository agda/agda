{-# OPTIONS --sized-types #-}

module SizedTypesScopeExtrusion where

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

data Empty : Set where

data Unit : Set where
  unit : Unit

Zero : (i : Size) -> Nat {i} -> Set
Zero ._ zero = Unit
Zero ._ (suc _) = Empty

bla : Set
bla = (x : Nat) -> (i : Size) -> Zero i x
