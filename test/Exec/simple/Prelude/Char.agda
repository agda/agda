module Prelude.Char where

open import Prelude.Bool

postulate
  Char : Set

{-# BUILTIN CHAR Char #-}
{-# COMPILED_TYPE Char Char #-}

private
  primitive
    primCharEquality : (c c' : Char) -> Bool


charEq : Char -> Char -> Bool
charEq = primCharEquality

