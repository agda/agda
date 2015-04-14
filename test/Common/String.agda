module Common.String where

open import Common.Bool
open import Common.Char
open import Common.List
open import Common.Nat
open import Common.Integer

postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

primitive
  primStringAppend   : String → String → String
  primStringToList   : String → List Char
  primStringFromList : List Char → String
  primStringEquality : String → String → Bool


strEq : (x y : String) -> Bool
strEq = primStringEquality

infixr 30 _+S+_

_+S+_ : (x y : String) -> String
_+S+_ = primStringAppend

fromList : List Char -> String
fromList = primStringFromList

fromString : String -> List Char
fromString = primStringToList

charToStr : Char → String
charToStr c = primStringFromList (c ∷ [])

private
  primitive
    primShowInteger  : Integer -> String
    primNatToInteger : Nat -> Integer

natToString : Nat -> String
natToString n = primShowInteger (primNatToInteger n)
