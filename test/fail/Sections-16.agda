module _ where

module A where

  data D : Set where
    !_ : D

module B where

  data D : Set where
    !_ : D

open A

test : B.D
test = !_
