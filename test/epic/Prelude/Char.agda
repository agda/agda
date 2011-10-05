module Prelude.Char where

open import Prelude.Bool

postulate
  Char : Set

{-# BUILTIN CHAR Char #-}

private
  primitive
    primCharEquality : (c c' : Char) -> Bool

postulate
  eof : Char

{-# COMPILED_EPIC eof () -> Int = foreign Int "eof" () #-}


charEq : Char -> Char -> Bool
charEq = primCharEquality

