-- Andreas, 2012-03-08
module NoNoTerminationCheck where

{-# NO_TERMINATION_CHECK #-}
f : Set
f = f

-- the pragma should not extend to the following definition

g : Set
g = g

-- error: non-termination

