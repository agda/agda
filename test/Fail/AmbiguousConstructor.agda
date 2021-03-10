module AmbiguousConstructor where

module Foo where
  data D : Set where
    c0 : D
    c1 : D

module Bar where
  open Foo public

data B : Set where
  tt : B
  ff : B

open Foo renaming (c0 to c2)
open Bar renaming (c1 to c2)

foo : D -> B
-- c2 is ambiguous: it could refer to c0 or c1.
foo c2 = tt
foo _ = ff
