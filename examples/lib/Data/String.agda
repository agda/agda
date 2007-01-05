
module Data.String where

import Data.List
import Data.Char
open   Data.List using (List)
open   Data.Char

postulate String : Set

{-# BUILTIN STRING String #-}

infixr 50 _++_

private
  primitive
    primStringAppend   : String -> String -> String
    primStringToList   : String -> List Char
    primStringFromList : List Char -> String

_++_     = primStringAppend
toList   = primStringToList
fromList = primStringFromList

