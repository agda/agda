-- Andreas, 2015-02-24, issue reported by g.x.allais
-- {-# OPTIONS -v interaction.give:100 #-}

record R : Set1 where
  field
    -v : Set

goal : R
goal = {!!}

-- refine here
-- WAS: error due to rendering or record as
--   record {-v = ?}
