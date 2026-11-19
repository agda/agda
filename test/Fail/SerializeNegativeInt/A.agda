module SerializeNegativeInt.A where

module M where
  data D : Set where
    c : D

module N (X : Set) where
  open M public

-- The display form generated for the copy of c here
-- has a negative number of pattern variables.

module _ (X : Set) where
  open N X public
