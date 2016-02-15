
module _ where

module M where
  postulate A : Set

module N = M  -- This alias introduces a display form M.A --> N.A

open M

postulate
  a : A

{-# DISPLAY N.A = A #-} -- Makes Agda loop

test : Set
test = a
