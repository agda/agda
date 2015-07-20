-- {-# OPTIONS -v tc.lhs:10 -v tc.lhs.split:50 #-}

postulate A : Set

record R : Set where
  field f : A

test : _ → A
test record{f = a} = a
-- This could succeed, but Agda currently does not try to guess
-- the type type of the record pattern from its field names.
