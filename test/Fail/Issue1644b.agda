
module _ where

module M where
  postulate A : Set

module N = M  -- This alias introduces a display form M.A --> N.A

open M

postulate
  a : A

{-# DISPLAY N.A = A #-}
  -- Makes Agda loop.
  -- Display form should be ignored with a warning.

test : Set
test = a

-- Should fail with error N.A !=< Set
