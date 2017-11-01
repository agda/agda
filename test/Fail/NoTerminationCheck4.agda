-- 2012-03-08 Andreas

{-# OPTIONS --warning=error #-}

module NoTerminationCheck4 where

data Bool : Set where
  true false : Bool

{-# NON_TERMINATING #-}
private
  f : Bool -> Bool
  f true = f true
  f false = f false

-- error: must place pragma before f
