module ExportAndUse where

data Bool : Set where
  true false : Bool

{-# COMPILE GHC Bool = data Bool (True | False) #-}

foo : Bool → Bool
foo true  = false
foo false = true

{-# COMPILE GHC foo as foohs #-}

test : Bool
test = foo true
