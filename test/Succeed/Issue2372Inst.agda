-- Andreas, 2017-01-01, issue 2372, reported by m0davis

-- This file is imported by Issue2372ImportInst.

module Issue2372Inst where

postulate D : Set

record R : Set₁ where
  field
    r : Set

open R {{ ... }} public

instance iR = record { r = D }
