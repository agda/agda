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

{-# COMPILE JS Char = String #-}
{-# COMPILE JS primCharEquality = x => y => x === y #-}
{-# COMPILE JS primIsLower = x => 'a' <= x && x <= 'z' #-}
{-# COMPILE JS primIsDigit = x => '0' <= x && x <= '9' #-}
{-# COMPILE JS primIsAlpha = x => ('a' <= x && x <= 'z') || ('A' <= x && x <= 'Z') #-}
{-# COMPILE JS primIsSpace = x => x === ' ' #-}
{-# COMPILE JS primIsAscii = x => x.codePointAt(0) < 128 #-}
{-# COMPILE JS primIsLatin1 = x => x.codePointAt(0) < 256 #-}
{-# COMPILE JS primIsPrint = x => x === ' ' || ('!' <= x && x <= '~') #-}
{-# COMPILE JS primIsHexDigit = x => '0' <= x && x <= '9' || 'a' <= x && x <= 'f' || 'A' <= x && x <= 'F' #-}
{-# COMPILE JS primToUpper = x => x.toUpperCase() #-}
{-# COMPILE JS primToLower = x => x.toLowerCase() #-}
{-# COMPILE JS primCharToNat = x => BigInt(x.codePointAt(0)) #-}
{-# COMPILE JS primNatToChar = function(x) {
    const y = x % 0x110000n;
    return 0xD800n <= y && y <= 0xDFFFn ? '�' : String.fromCharCode(Number(y));
} #-}
