-- Andreas, 2012-03-08
module NoNoTerminationCheck where

{-# NON_TERMINATING #-}
f : Set
f = f

-- the pragma should not extend to the following definition

g : Set
g = g

-- error: non-termination

