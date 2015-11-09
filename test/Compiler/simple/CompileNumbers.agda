{-# OPTIONS -v treeless.opt:20 #-}
module _ where

open import Common.Prelude
open import Common.Integer

-- Should compile to
--   λ a b → case a of
--              "neg" → 0 - b
--              _     → b
match-on-lit : String → Integer → Integer
match-on-lit "neg" x with x
...                     | pos (suc n) = negsuc n
...                     | pos 0       = pos 0
...                     | negsuc n    = pos (suc n)
match-on-lit _     x = x

-- This doesn't compile as nicely, since the match on "neg"
-- ends up between the match on the int and the nat (not sure why).
match-on-lit₂ : String → Integer → Integer
match-on-lit₂ "neg" (pos (suc n)) = negsuc n
match-on-lit₂ "neg" (negsuc n)    = pos (suc n)
match-on-lit₂ _     x             = x

-- Should compile to a flat case
nested-match : Integer → String
nested-match (pos 0) = "zero"
nested-match (pos 1) = "one"
nested-match (pos (suc (suc n))) = "lots"
nested-match (negsuc 0) = "minus one"
nested-match (negsuc 1) = "minus two"
nested-match (negsuc (suc (suc n))) = "minus lots"

printInt : Integer → IO Unit
printInt x = putStrLn (intToString x)

main : IO Unit
main = printInt (match-on-lit "neg" (pos 42))
    ,, printInt (match-on-lit₂ "neg" (pos 42))
    ,, putStrLn (nested-match (negsuc 5))
