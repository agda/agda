module Common.Float where

open import Common.String

postulate
  Float : Set


{-# BUILTIN FLOAT Float #-}

private
  primitive
    primShowFloat : Float -> String

floatToString : Float  -> String
floatToString = primShowFloat
