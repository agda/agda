module Prelude.Float where

open import Prelude.String

postulate
  Float : Set
  floatToString : Float  -> String
  stringToFloat : String -> Float

{-# BUILTIN FLOAT Float #-}
{-# COMPILED_EPIC floatToString (f : Float) -> String = frString(floatToStr(f)) #-}
{-# COMPILED_EPIC stringToFloat (s : Any) -> Float = strToFloat(mkString(s)) #-}