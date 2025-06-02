-- If this is the Main file and no interfaces  A2 and B2 exist yet, Agda fails.
-- If A2 is processed first, this will load A1 which makes B2 fail.
-- If B2 is processed first, this will load B1 which makes A2 fail.
-- Only if A2 and B2 are checked independently, both succeed.

module Main where

open import Base
import A2 -- rewrite for c
import B2 -- rewrite for d

thm : c ≡ d
thm = refl
