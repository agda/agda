module Using where

module Dummy where
  data DummySet1 : Set where ds1 : DummySet1
  data DummySet2 : Set where ds2 : DummySet2

open Dummy
  using (DummySet1)

open Dummy -- checking that newline + comment is allowed before "using"
  using (DummySet2)

-- Andreas, 2020-06-06, issue #4704
-- Allow repetions in `using` directives, but emit warning.
open Dummy
  using (DummySet1; DummySet1)
  using (DummySet1)

-- EXPECTED: dead code highlighting for 2nd and 3rd occurrence and warning:
-- Duplicates in using directive: DummySet1 DummySet1
-- when scope checking the declaration
--   open Dummy using (DummySet1; DummySet1; DummySet1)
