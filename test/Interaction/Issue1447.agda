-- Andreas, 2015-02-26
-- {-# OPTIONS -v interaction:100 #-}

data D : Set where
  c : D

goal : D
goal = {! !}  -- C-c C-r gave a parse error here, as there was a (single) space.

g1 : D
g1 = {!  !}

g2 : D
g2 = {!   !}

-- works now
