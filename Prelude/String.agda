------------------------------------------------------------------------
-- Strings
------------------------------------------------------------------------

module Prelude.String where

open import Prelude.List using ([_])

------------------------------------------------------------------------
-- The type

postulate
  String : Set
  Char   : Set

{-# BUILTIN STRING String #-}
{-# BUILTIN CHAR   Char   #-}

private
 primitive
  primStringAppend   : String -> String -> String
  primStringToList   : String -> [ Char ]
  primStringFromList : [ Char ] -> String

_++_ : String -> String -> String
_++_ = primStringAppend

toList : String -> [ Char ]
toList = primStringToList

fromList : [ Char ] -> String
fromList = primStringFromList
