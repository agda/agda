-- Andreas, 2015-02-07

postulate
  X Y : Set
  fix : (X → X) → X
  g   : Y → X → X
  y   : Y
  P   : X → Set
  yes : (f : X → X) → P (f (fix f))

test : P (g y (fix (g y)))
test with g y
test | f = yes f

-- should be able to abstract (g y) twice
-- and succeed
