-- Andreas, issue 2349

-- Andreas, 2016-12-20, issue #2350

-- {-# OPTIONS -v tc.term.con:50 #-}

postulate A : Set

data D {{a : A}} : Set where
  c : D

test : {{a b : A}} → D
test {{a}} = c {{a}}

-- WAS: complaint about unsolvable instance

-- Should succeed
