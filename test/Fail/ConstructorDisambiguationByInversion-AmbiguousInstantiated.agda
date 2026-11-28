-- Both module instances bring the same original constructor `Foo.D.c` into
-- scope, with different module arguments.  The possible indices are
-- `tag true` and `tag false`.  A single constructor name and datatype name
-- in the original module therefore do not determine a unique candidate.

module ConstructorDisambiguationByInversion-AmbiguousInstantiated where

open import Agda.Builtin.Bool using (Bool ; false ; true)

module Foo (b : Bool) where
  data D : Set where
    c : D

open Foo true using (c)
open Foo false using (c)

data Index : Set where
  tag : Bool → Index

El : Index → Set
El (tag b) = Foo.D b

index : ∀ {i} → El i → Index
index {i} _ = i

test : Index
test = index c  -- Both instances of `Foo.D.c` are possible.
