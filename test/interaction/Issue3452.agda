
data ⊤ : Set where tt : ⊤

record R : Set where
  constructor r
  field .x : ⊤

f : R → R
R.x (f (r x)) = {!x!}
