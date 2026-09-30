-- Andreas, 2016-07-01 issue #2078
-- Holes in postponed type-checking problems cannot be worked on.

-- {-# OPTIONS -v interaction:30 #-}
-- {-# OPTIONS -v tc.term.exlam:30 -v tc:5 #-}

test : Set → Set
test A = (λ{ B → {!B!}}) A

-- splitting on B gives
-- No type nor action available for hole ?0
