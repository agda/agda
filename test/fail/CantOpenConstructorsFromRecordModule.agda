
module CantOpenConstructorsFromRecordModule where

module Datatypes where
  record Foo : Set where
    constructor foo

ok : Datatypes.Foo
ok = Datatypes.foo

open Datatypes.Foo

bad : Datatypes.Foo
bad = foo