-- Andreas, 2019-11-08, issue #4154 reported by Yashmine Sharoda.

-- Warn if a `renaming` clause clashes with an exported name
-- (that is not mentioned in a `using` clause).

module _ where

module M where
  postulate
    A B : Set

-- These produce warnings (#4154):

module N = M renaming (A to B)
open M renaming (A to B)

-- These produce errors (see also #3057)
-- as they produce ambiguous exports:

Test = B
TestN = N.B
module L = M using (B) renaming (A to B)
