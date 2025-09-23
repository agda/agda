{-# OPTIONS --cubical-compatible --safe --no-universe-polymorphism
            --no-sized-types --no-guardedness --level-universe #-}

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

{-# COMPILE JS uprimCharEquality = (x, y) => x === y #-}
{-# COMPILE JS PrimCharEquality = x => y => x === y #-}
{-# COMPILE JS PrimIsLower = x => 'a' <= x && x <= 'z' #-}
{-# COMPILE JS PrimIsDigit = x => '0' <= x && x <= '9' #-}
{-# COMPILE JS PrimIsAlpha = x => ('a' <= x && x <= 'z') || ('A' <= x && x <= 'Z') #-}
{-# COMPILE JS PrimIsSpace = x => x === ' ' #-}
{-# COMPILE JS PrimIsAscii = x => x.codePointAt(0) < 128 #-}
{-# COMPILE JS PrimIsLatin1 = x => x.codePointAt(0) < 256 #-}
{-# COMPILE JS PrimIsPrint = x => x === ' ' || ('!' <= x && x <= '~') #-}
{-# COMPILE JS PrimIsHexDigit = x => '0' <= x && x <= '9' || 'a' <= x && x <= 'f' || 'A' <= x && x <= 'F' #-}
{-# COMPILE JS PrimToUpper = x => x.toUpperCase() #-}
{-# COMPILE JS PrimToLower = x => x.toLowerCase() #-}
{-# COMPILE JS PrimCharToNat = x => BigInt(x.codePointAt(0)) #-}
{-# COMPILE JS PrimCharToNatInjective = x => BigInt(x.codePointAt(0)) #-}
{-# COMPILE JS PrimNatToChar = x => String.fromCodePoint(Number(x)) #-}
{-# COMPILE JS primCharToNat = x => BigInt(x.codePointAt(0)) #-}
