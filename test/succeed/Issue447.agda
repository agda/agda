-- Abstract definitions can't be projection-like
module Issue447 where

postulate
  I : Set
  R : I → Set

module M (i : I) (r : R i) where

  abstract

    P : Set₂
    P = Set₁

    p : P
    p = Set
