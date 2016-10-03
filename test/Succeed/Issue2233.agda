-- Andreas, 2016-10-03, issue #2233
-- Positivity check should return the same result when change
-- all involved definitions from non-abstract to abstract.

abstract
  data Functor : Set where
    Id : Functor

  _·_ : Functor → Set → Set
  Id · A = A

  data ν (F : Functor) : Set where
    inn : F · ν F → ν F

-- Should positivity check ok.
