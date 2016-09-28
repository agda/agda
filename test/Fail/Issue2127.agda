-- Andreas, 2016-08-02 issue #2127 reported by petercommand

data Test : Set₁ where
  field
    A : Set
    B : Set  -- second field necessary to trigger internal error

-- WAS: internal error

-- Should give proper error
