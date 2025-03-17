module Issue7751 where

module M (X : Set) where
  data X' : Set where

Bad : Set
open M Bad
Bad = X'
