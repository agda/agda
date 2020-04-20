module Issue4130 where

module Foo where
  data D : Set where
    con : D

module Bar (S : Set) where
  open Foo public using (con)

open Bar using (con)
open Foo using (D; con)

data B : Set where
  tt : B
  ff : B

module _ (S : Set) where
  open Bar S
  f : D -> B
  -- 'con' is not ambiguous, because although 'con' may refer to
  -- 'Foo.D.con' or 'Bar.con', they are two different names of the
  -- same constructor.
  f con = tt
