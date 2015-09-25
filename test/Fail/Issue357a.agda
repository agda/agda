
module Issue357a where

module M (X : Set) where

  data R : Set where
    r : X → R

postulate
  P Q : Set
  q   : Q

open M P
open M.R

works : M.R Q → Q
works (M.R.r q) = q

fails : M.R Q → Q
fails (r q) = q
