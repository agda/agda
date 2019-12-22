{-# OPTIONS --allow-unsolved-metas #-}

postulate
  A : Set
  R : A → Set
  M : (a : A) (s t : R a) → Set

variable
  a : A
  s : R a

t : _

postulate
  m : M _ s t

t = _
