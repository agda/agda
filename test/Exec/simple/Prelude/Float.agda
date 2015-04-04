module Prelude.Float where

open import Prelude.String

postulate
  Float : Set


{-# BUILTIN FLOAT Float #-}

private
  primitive
    primShowFloat : Float -> String

floatToString : Float  -> String
floatToString = primShowFloat
