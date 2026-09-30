-- Andreas, 2016-10-06 issue #2239

-- We need to subtract number of locals when computing
-- de Bruijn index of split variable!

-- {-# OPTIONS -v interaction.case:50 #-}

data Bool : Set where
  true false : Bool

test : (x y z : Bool) → Bool
test x y = λ z → {!y !}  -- splitting on y should succeed

fails : (x y z : Bool) → Bool
fails x y = λ z → {!z !}  -- splitting on z should fail
