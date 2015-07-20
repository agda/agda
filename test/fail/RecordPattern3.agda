-- {-# OPTIONS -v tc.lhs:10 -v tc.lhs.split:50 #-}

postulate A : Set

record R : Set where
  field f : A

record S : Set where
  field f : A

test : _ → A
test record{f = a} = a
