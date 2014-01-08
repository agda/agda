{-# OPTIONS --allow-unsolved-metas #-}
postulate
  A : Set
  a : A

record Q .(x : A) : Set where
  field q : A

record R : Set where
  field s : Q _

  t : A
  t = Q.q s
