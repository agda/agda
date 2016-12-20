-- Andreas, 2016-11-02, issue #2289
-- Meta should be acceptable as sort of record type.

postulate
  F : Set → Set

mutual
  data ⊥ : _ where  -- works

  FBot = F ⊥

mutual
  record ⊤ : _ where  -- should work

  FTop = F ⊤
