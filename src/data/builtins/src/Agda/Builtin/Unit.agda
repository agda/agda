
module Agda.Builtin.Unit where

record ⊤ : Set where
  instance constructor tt

{-# BUILTIN UNIT ⊤ #-}
{-# COMPILED_DATA ⊤ () () #-}
