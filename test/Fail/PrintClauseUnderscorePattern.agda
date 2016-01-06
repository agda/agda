-- Andreas 2016-01-06

-- {-# OPTIONS -v error.checkclause:60 #-}

data D : Set where
  c : D

test : (x y z : D) → Set
test _ c _ with D
test x y z | _ = D

-- Expected output: clause should be printed as is in error message,
-- including underscore patterns.
