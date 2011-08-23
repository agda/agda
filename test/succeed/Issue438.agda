{-
  There was a bug when partially instantiating a module containing
  record projections.
-}
module Issue438 where

module M (A : Set) where

  record R (a : A) : Set₁ where
    field
      S : Set

postulate
  X : Set
  x : X
  r : M.R X x

module MX = M X

postulate
  T : MX.R.S r → Set
  y : M.R.S X r
  t : T y
