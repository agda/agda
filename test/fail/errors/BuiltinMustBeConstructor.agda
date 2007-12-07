
module BuiltinMustBeConstructor where

postulate Nat : Set

suc : Nat -> Nat
suc x = x

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN SUC suc #-}
