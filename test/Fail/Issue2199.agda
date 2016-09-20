-- Andreas, 2016-09-20, issue #2199, reported by Favonia

module _ where

module _ where
  private  -- This private is useless!
    module _ where
      postulate
        A : Set

test = A
