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
{-# COMPILE GHC _-_ = (-) #-}
{-# COMPILE JS  _-_ = function(x) { return function(y) { return agdaRTS.uprimIntegerMinus(x, y); }; } #-}

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

fancyCase : Nat → Cmp → Nat
fancyCase 0 _ = 0
fancyCase (suc (suc (suc n))) greater = n
fancyCase (suc (suc (suc _))) equal = 4
fancyCase 1 _ = 1
fancyCase 2 _ = 2
fancyCase (suc n) less = n

main : IO Unit
main = putStrLn (cmp (pos 31) (negsuc 5)) ,,
       putStrLn (cmp (pos 5) (pos 5)) ,,
       putStrLn (cmp (negsuc 4) (negsuc 2))
