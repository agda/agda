
module Issue357 where

module M (X : Set) where

  data R : Set where
    r : X → R

postulate
  P Q : Set
  q   : Q

open M P
open M.R

works : M.R Q
works = M.R.r q

fails : M.R Q
fails = r q
