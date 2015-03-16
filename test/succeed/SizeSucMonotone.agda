-- Andreas, 2012-09-24 Ensure that size successor is monotone

-- Andreas, 2015-03-16 SizeUniv is still imperfect, so we need type-in-type
-- here to work around the conflation of sLub and the PTS rule.
{-# OPTIONS --type-in-type #-}

module SizeSucMonotone where

open import Common.Size

data Bool : Set where
  true false : Bool

-- T should be monotone in its second arg
T : Bool → Size → Set
T true  i = (Size< i     → Bool) → Bool
T false i = (Size< (↑ i) → Bool) → Bool

test : {x : Bool}{i : Size}{j : Size< i} → T x j → T x i
test h = h

