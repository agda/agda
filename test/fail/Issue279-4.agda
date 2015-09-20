module Issue279-4 where

module M (X : Set) where

  data R : Set where
    r : X → R

postulate
  P Q : Set

open M P using (r)

shouldn't-check : M.R Q → Q
shouldn't-check (r q) = q
