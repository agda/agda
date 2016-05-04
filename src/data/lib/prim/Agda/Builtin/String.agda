{-# OPTIONS --without-K #-}

module Agda.Builtin.String where

open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Char

postulate String : Set
{-# BUILTIN STRING String #-}

primitive
  primStringToList   : String → List Char
  primStringFromList : List Char → String
  primStringAppend   : String → String → String
  primStringEquality : String → String → Bool
  primShowChar       : Char → String
  primShowString     : String → String
