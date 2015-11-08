-- {-# OPTIONS -v term:20 -v tc.term:20  #-}
-- {-# OPTIONS -v tc.def.alias:100 -v tc.term.expr.coind:100 #-}
module Issue807 where

open import Common.Coinduction

data Stream : Set where
  cons : ∞ Stream → Stream

mutual

  -- s : Stream
  s = cons s′

  -- s′ : ∞ _
  s′ = ♯ s

-- Under 2.3.0.1: The code is accepted.
-- Under 2.3.2:   The termination checker complains.

-- Bug was that aliases did not lead to construction of ♯-auxiliary function.
