-- Andreas, 2012-09-24 Ensure that size successor is monotone
{-# OPTIONS --sized-types #-}
module SizeSucMonotone where

open import Common.Size

postulate Size< : Size → Set
{-# BUILTIN SIZELT Size< #-}

data Bool : Set where
  true false : Bool

-- T should be monotone in its second arg
T : Bool → Size → Set
T true  i = Size< i
T false i = Size< (↑ i)

test : {x : Bool}{i : Size}{j : Size< i} → T x j → T x i
test h = h

