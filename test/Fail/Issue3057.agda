-- Andreas, 2018-06-03, issue #3057 reported by nad.
-- We should not allow the public import of an ambiguous identifier

-- {-# OPTIONS -v scope:20 #-}

module Issue3057 where

module M where

  postulate
    A : Set
    a : A

open M public renaming (a to A)

-- Should fail
