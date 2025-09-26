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
{-# COMPILE JS primIsLower = x => /\p{Ll}/u.test(x) #-} -- Ll stands for Lowercase letters
{-# COMPILE JS primIsDigit = x => /\d/u.test(x) #-}
{-# COMPILE JS primIsAlpha = x => /\p{L}/u.test(x) #-} -- L stands for Letters
{-# COMPILE JS primIsSpace = x => /\p{space}/u.test(x) #-}
{-# COMPILE JS primIsAscii = x => x.codePointAt(0) < 128 #-}
{-# COMPILE JS primIsLatin1 = x => x.codePointAt(0) < 256 #-}
{-# COMPILE JS primIsPrint = x => !/[\p{Cc}\p{Cf}]/u.test(x) #-}
{-# COMPILE JS primIsHexDigit = x => /\p{AHex}/u.test(x) #-} -- AHex stands for ASCII Hexadecimal digits
{-# COMPILE JS primToUpper = x => x.toUpperCase() #-}
{-# COMPILE JS primToLower = x => x.toLowerCase() #-}
{-# COMPILE JS primCharToNat = x => BigInt(x.codePointAt(0)) #-}
{-# COMPILE JS primNatToChar = function(x) {
    const y = x % 0x110000n;
    return 0xD800n <= y && y <= 0xDFFFn ? '�' : String.fromCodePoint(Number(y));
} #-}
