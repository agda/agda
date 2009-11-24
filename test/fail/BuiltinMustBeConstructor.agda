
module BuiltinMustBeConstructor where

data Nat : Set where
  zero : Nat
  one  : Nat

suc : Nat -> Nat
suc x = x

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN SUC suc #-}
