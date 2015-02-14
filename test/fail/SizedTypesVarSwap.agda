{-# OPTIONS --sized-types #-}

module SizedTypesVarSwap where

open import Common.Size renaming (↑_ to _^)

data Nat : {size : Size} -> Set where
  zero : {size : Size} -> Nat {size ^}
  suc  : {size : Size} -> Nat {size} -> Nat {size ^}

bad : {i j : Size} -> Nat {i} -> Nat {j} -> Nat {∞}
bad (suc x) y = bad (suc y) x
bad zero y = y
