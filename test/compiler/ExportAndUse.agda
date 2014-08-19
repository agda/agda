module ExportAndUse where

data Bool : Set where
  true false : Bool

{-# COMPILED_DATA Bool Bool True False #-}

foo : Bool → Bool
foo true  = false
foo false = true

{-# COMPILED_EXPORT foo foohs #-}

test : Bool
test = foo true
