postulate A : Set

record R : Set where
  field f f' : A

record S : Set where
  field g g' : A

test : R → A
test record{g = a; g' = a'} = a
