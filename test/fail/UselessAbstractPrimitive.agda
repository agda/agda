module UselessAbstractPrimitive where

postulate Int : Set

{-# BUILTIN INTEGER Int #-}

abstract
  primitive
    primIntegerPlus : Int -> Int -> Int
