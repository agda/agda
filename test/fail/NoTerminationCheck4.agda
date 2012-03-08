-- 2012-03-08 Andreas
module NoTerminationCheck4 where

data Bool : Set where
  true false : Bool

{-# NO_TERMINATION_CHECK #-}
private
  f : Bool -> Bool
  f true = f true
  f false = f false

-- error: must place pragma before f
