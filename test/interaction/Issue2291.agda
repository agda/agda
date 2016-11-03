-- Andreas, 2016-11-03, issue #2291, reported by Aerate

-- {-# OPTIONS -v interaction.helper:100 #-}

record Foo : Set where
  coinductive
  field one : Foo
open Foo

someFoo : Foo
someFoo .one = {! {R} -> Foo.one R !}

-- WAS: C-c C-h gives:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/Syntax/Translation/ConcreteToAbstract.hs:1248

-- NOW:
-- Expected an argument of the form f e1 e2 .. en
-- when checking that the expression ? has type Foo
