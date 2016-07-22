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

{-# COMPILED_JS primStringToList function(x) { return x.split(""); } #-}
{-# COMPILED_JS primStringFromList function(x) { return x.join(""); } #-}
{-# COMPILED_JS primStringAppend function(x) { return function(y) { return x+y; }; } #-}
{-# COMPILED_JS primStringEquality function(x) { return function(y) { return x===y; }; } #-}
{-# COMPILED_JS primShowChar function(x) { return x; } #-}
{-# COMPILED_JS primShowString function(x) { return x; } #-}
