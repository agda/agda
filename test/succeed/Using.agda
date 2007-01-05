module Using where

module Dummy where
  data DummySet1 : Set where ds1 : DummySet1
  data DummySet2 : Set where ds2 : DummySet2

open Dummy
  using (DummySet1)

open Dummy -- checking that newline + comment is allowed before "using"
  using (DummySet2)
