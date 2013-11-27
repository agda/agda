
module BuiltinMustBeConstructor where

data Bool : Set where
  true  : Bool
  other : Bool

false : Bool
false = true

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}
