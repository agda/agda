-- 2011-09-09, submitted by mokus.4...@gmail.com
-- This bug report wins the first price in the false golfing tournament!
-- {-# OPTIONS -v term:20 #-}
module Issue444 where

data ⊥ : Set where

relevant : .⊥ → ⊥
relevant ()

false : ⊥
false = relevant false
