-- {-# OPTIONS -v impossible:100 #-}
-- 2013-06-15 Andreas, reported by evancavallo
module Issue870 where

{- The following fails with

  An internal error has occurred. Please report this as a bug.
  Location of the error: src/full/Agda/TypeChecking/Rules/Term.hs:421

in Agda 2.3.3 on Ubuntu. Works fine using Set instead of Type or after tweaking the definition of test into a more sensible form. -}

Type = Set

data ⊤ : Type where
  tt : ⊤

record R : Type
  where
  field
    a : ⊤

test : ⊤ → R
test t = (λ a → record {a = a}) t

-- There was a possible __IMPOSSIBLE__ in the code for
-- guessing the record type of record{a = a}.
-- The problem was that a defined sort like Type, needs to be
-- reduced.
