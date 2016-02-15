
module _ where

postulate
  A B : Set

{-# DISPLAY A = B #-}
{-# DISPLAY B = A #-}

loop : A
loop = {!!}
