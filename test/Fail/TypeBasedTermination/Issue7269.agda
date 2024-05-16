-- Andreas, 2024-05-16, issue #7269
-- --no-syntax-based-termination should not turn on --type-based-termination

{-# OPTIONS --safe #-}
{-# OPTIONS --no-type-based-termination #-}
{-# OPTIONS --no-syntax-based-termination #-}  -- Turns on TBT, but should not

-- {-# OPTIONS -v term.tbt:50 #-}

module TypeBasedTermination.Issue7269 where

record U : Set where
  coinductive
  field force : U
open U

-- This should not pass since no termination checker is on.
u : U
u .force = u
