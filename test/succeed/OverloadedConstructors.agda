
module OverloadedConstructors where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc  : {n : Nat} -> Fin n -> Fin (suc n)

three : Nat
three = suc (suc (suc zero))

ftwo : Fin three
ftwo = suc (suc zero)

inc : Nat -> Nat
inc = suc

{-
{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}
-}
