-- 2012-03-08 Andreas
module NoTerminationCheck3 where

data Bool : Set where
  true false : Bool

f : Bool -> Bool
f true = true
{-# TERMINATING #-}
f false = false

-- error: cannot place pragma inbetween clauses
