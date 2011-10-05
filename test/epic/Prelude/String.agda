module Prelude.String where

open import Prelude.Bool
open import Prelude.Char
open import Prelude.List
open import Prelude.Nat

postulate
  String : Set
  nil : String
  primStringToNat : String → Nat
  charToString : Char -> String

{-# BUILTIN STRING String #-}

primitive
  primStringAppend   : String → String → String
  primStringToList   : String → List Char
  primStringFromList : List Char → String
  primStringEquality : String → String → Bool

{-# COMPILED_EPIC nil () -> String = "" #-} 
{-# COMPILED_EPIC primStringToNat (s : String) -> BigInt = foreign BigInt "strToBigInt" (s : String) #-}
-- {-# COMPILED_EPIC charToString (c : Int) -> String = charToString(c) #-}

strEq : (x y : String) -> Bool
strEq = primStringEquality

infixr 30 _+S+_

_+S+_ : (x y : String) -> String
_+S+_ = primStringAppend

fromList : List Char -> String
fromList = primStringFromList

fromString : String -> List Char
fromString = primStringToList