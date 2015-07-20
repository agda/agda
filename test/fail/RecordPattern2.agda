postulate A : Set

record R : Set where
  field f : A

record S : Set where
  field g : A

test : R → A
test record{g = a} = a
