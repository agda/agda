
mutual
  data D : Set where
    c : R → D

  record R : Set where
    inductive
    field
      out : D
open R

f : D → {A : Set} → A
f (c x) = f (out x)
-- should termination check

