-- Andreas, 2013-03-22
-- {-# OPTIONS -v tc.lhs:40 #-}
module Issue279-3 where

module M (X : Set) where

  data R : Set where
    r : X → R

postulate
  P Q : Set

open M P

shouldn't-check : M.R Q → Q
shouldn't-check (r q) = q

-- Agda uses the type of the original constructor
--
--   M.r {X : Set} : X → R X
--
-- instead of the type of the copied constructor
--
--   r : P → R
--
-- If one changes the domain to _, it will be resolved to
-- R, which is M.R P, and q gets assigned type P, leading
-- to expected failure.

-- Fixed this issue by comparing the parameter reconstructed
-- from the domain, Q, to the parameter of the unambiguous
-- constructor r, which is P.
