
postulate A : Set

record R : Set where
  constructor r
  field f : A

test : R → R
test x = let r a = x
             foo : R → A
             foo x = let r a = x in a
         in r (foo (r a))
