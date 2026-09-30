-- 2014-01-15 Andreas, reported by fredrik.forsberg

data Unit : Set where
  tt : Unit

foo : Unit
foo = {!!}
-- Refine here should give tt
