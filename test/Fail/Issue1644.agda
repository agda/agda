-- {-# OPTIONS -v tc.display:20 #-}
-- {-# OPTIONS -v tc.display.recursive:90 #-}

postulate
  A B : Set

{-# DISPLAY A = B #-}
{-# DISPLAY B = A #-}

loop : A
loop = {!!}

-- Should fail with unsolved metas.
