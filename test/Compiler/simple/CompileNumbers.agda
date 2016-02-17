{-# OPTIONS -v treeless.opt:20 #-}
module _ where

open import Agda.Builtin.Nat using (_<_)
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

data Diff : Set where
  less : Nat → Diff
  equal : Diff
  greater : Nat → Diff

compareNat : Nat → Nat → Diff
compareNat a b with a < b
... | true = less (b ∸ suc a)
... | false with b < a
...   | true  = greater (a ∸ suc b)
...   | false = equal
{-# INLINE compareNat #-}

-- Should compile to 0 - a
neg : Nat → Integer
neg zero    = pos zero
neg (suc a) = negsuc a
{-# INLINE neg #-}

-- Should compile to a - b
_-N_ : Nat → Nat → Integer
a -N b with compareNat a b
... | less k    = negsuc k
... | equal     = pos (a ∸ b)
... | greater k = pos (suc k)
{-# INLINE _-N_ #-}

-- Should compile to a + b
_+Z_ : Integer → Integer → Integer
pos    a +Z pos    b = pos (a + b)
pos    a +Z negsuc b = a -N suc b
negsuc a +Z pos    b = b -N suc a
negsuc a +Z negsuc b = negsuc (suc a + b)
{-# INLINE _+Z_ #-}

-- Should compile to a * b
_*Z_ : Integer → Integer → Integer
pos    a *Z pos    b = pos (a * b)
pos    a *Z negsuc b = neg (a * suc b)
negsuc a *Z pos    b = neg (suc a * b)
negsuc a *Z negsuc b = pos (suc a * suc b)
{-# INLINE _*Z_ #-}

printInt : Integer → IO Unit
printInt x = putStrLn (intToString x)

main : IO Unit
main = printInt (match-on-lit "neg" (pos 42))
    ,, printInt (match-on-lit₂ "neg" (pos 42))
    ,, putStrLn (nested-match (negsuc 5))
