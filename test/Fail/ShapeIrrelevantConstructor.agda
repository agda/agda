-- Andreas, 2018-06-14, issue #2513, surviving shape-irrelevance annotations.

data Wrap (A : Set) : Set where
  @shape-irrelevant wrap : A → Wrap A
