------------------------------------------------------------------------
-- The Agda standard library
--
-- Core definitions for Strings
------------------------------------------------------------------------

module Data.String.Core where

open import Data.List using (List)
open import Data.Bool.Minimal using (Bool)
open import Data.Char.Core using (Char)

------------------------------------------------------------------------
-- The type

postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

------------------------------------------------------------------------
-- Primitive operations

primitive
  primStringAppend   : String → String → String
  primStringToList   : String → List Char
  primStringFromList : List Char → String
  primStringEquality : String → String → Bool
  primShowString     : String → String

  -- Here instead of Data.Char.Core to avoid an import cycle
  primShowChar       : Char → String
