{-# OPTIONS --sized-types #-}

module SizedTypesRigidVarClash where

open import Common.Size renaming (↑_ to _^)

data Nat : {size : Size} -> Set where
  zero : {size : Size} -> Nat {size ^}
  suc  : {size : Size} -> Nat {size} -> Nat {size ^}

inc : {i j : Size} -> Nat {i} -> Nat {j ^}
inc x = suc x
