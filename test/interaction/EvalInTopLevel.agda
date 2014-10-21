-- Andreas, 2014-10-18 AIM XX

module EvalInTopLevel where

data Bool : Set where true false : Bool

not : Bool → Bool
not true = false
not false = true

-- Evaluate @not false@ in top level.
