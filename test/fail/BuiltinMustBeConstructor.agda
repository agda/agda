
module BuiltinMustBeConstructor where

data Nat : Set where

suc : Nat -> Nat
suc x = x

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN SUC suc #-}
