module Prelude.String where

open import Prelude.Bool
open import Prelude.Char
open import Prelude.List
open import Prelude.Nat
open import Prelude.Integer

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
charToStr c = primStringFromList (c :: [])

primitive
  primShowInteger  : Integer -> String

natToString : Nat -> String
natToString n = primShowInteger (primNatToInteger n)
