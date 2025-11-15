
module _ where

data D .(A : Set) : Set

-- The dot should not be repeated here
data D .A where
  mkD : D A
