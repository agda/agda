
record Unit : Set where
  constructor tt

postulate
  C : Set
  c : C

g : C

f : Unit → C
f tt = c

record R : Set where
  constructor r

g = c
