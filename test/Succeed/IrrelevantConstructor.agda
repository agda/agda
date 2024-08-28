-- Andreas, 2016-02-11. Irrelevant constructors are not (yet?) supported

data D : Set where
  .c : D

-- warning: -W[no]FixingRelevance

-- Andreas, 2018-06-14, issue #2513, surviving shape-irrelevance annotations.

data Wrap (A : Set) : Set where
  @shape-irrelevant wrap : A → Wrap A
