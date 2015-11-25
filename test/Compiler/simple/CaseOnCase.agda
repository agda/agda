{-# OPTIONS -v treeless.opt:20 #-}
-- Tests for case-on-case simplification.
module _ where

open import Common.Prelude
open import Common.Integer

data Cmp : Set where
  less equal greater : Cmp

isLess : Cmp → Bool
isLess less = true
isLess equal = false
isLess greater = false
{-# INLINE isLess #-}

postulate _-_ : Integer → Integer → Integer
{-# COMPILED _-_ (-) #-}
{-# COMPILED_UHC _-_ UHC.Agda.Builtins.primIntegerMinus #-}

compareInt : Integer → Integer → Cmp
compareInt a b with a - b
... | pos 0       = equal
... | pos (suc _) = greater
... | negsuc _    = less
{-# INLINE compareInt #-}

_<_ : Integer → Integer → Bool
a < b = isLess (compareInt a b)
{-# INLINE _<_ #-}

cmp : Integer → Integer → String
cmp a b with a < b
... | true  = "less"
... | false = "not less"

main : IO Unit
main = putStrLn (cmp (pos 31) (negsuc 5)) ,,
       putStrLn (cmp (pos 5) (pos 5)) ,,
       putStrLn (cmp (negsuc 4) (negsuc 2))
