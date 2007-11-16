------------------------------------------------------------------------
-- Strings
------------------------------------------------------------------------

module Data.String where

open import Data.List using ([_])
open import Data.Char using (Char)
open import Data.Bool

------------------------------------------------------------------------
-- The type

postulate
  String : Set

{-# BUILTIN STRING String #-}

private
 primitive
  primStringAppend   : String -> String -> String
  primStringToList   : String -> [ Char ]
  primStringFromList : [ Char ] -> String
  primStringEquality : String -> String -> Bool

_++_ : String -> String -> String
_++_ = primStringAppend

toList : String -> [ Char ]
toList = primStringToList

fromList : [ Char ] -> String
fromList = primStringFromList

infix 4 _==_

_==_ : String -> String -> Bool
_==_ = primStringEquality
