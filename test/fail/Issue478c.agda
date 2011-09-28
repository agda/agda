
module Issue478c where

record Ko (Q : Set) : Set₁ where
 field
  T : Set

foo : (Q : Set)(ko : Ko Q) → Ko.T ko
foo Q ko = Set

-- We should make sure not to destroy printing
-- outside the record module. Type should be
-- printed as it's given: Ko.T ko