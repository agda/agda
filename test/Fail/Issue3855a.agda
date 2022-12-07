-- Andreas, 2019-06-17, LAIM 2019, issue #3855
-- Only allow erased definitions in erased context.

{-# OPTIONS --erasure #-}

open import Common.IO
open import Common.Unit
open import Common.String
open import Common.Bool

@0 noWorld : String
noWorld = "Hallo, Welt!"

-- Illegal definition, should raise a type error.

world : Bool → String
world true  = "Hello world!"
world false = noWorld

main = putStrLn (world false)
