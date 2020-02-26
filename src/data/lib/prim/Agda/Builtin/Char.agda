{-# OPTIONS --without-K --safe --no-universe-polymorphism
            --no-sized-types --no-guardedness --no-subtyping #-}

module Agda.Builtin.Char where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

postulate Char : Set
{-# BUILTIN CHAR Char #-}

primitive
  primIsLower primIsDigit primIsAlpha primIsSpace primIsAscii
    primIsLatin1 primIsPrint primIsHexDigit : Char → Bool
  primToUpper primToLower : Char → Char
  primCharToNat : Char → Nat
  primNatToChar : Nat → Char
  primCharEquality : Char → Char → Bool
