postulate
  A : Set

record R : Set where
  field
    a : A
  b : A
  b = a
open R

test : A
test = b
