
-- Shadowing is allowed.
module Shadow where

module M (A : Set) where

  id : Set -> Set
  id A = A

