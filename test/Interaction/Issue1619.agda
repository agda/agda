-- Andreas, 2015-08-11, issue reported by G.Allais

-- The `a` record field of `Pack` is identified as a function
-- (coloured blue, put in a \AgdaFunction in the LaTeX backend)
-- when it should be coloured pink.
-- The problem does not show up when dropping the second record
-- type or removing the module declaration.

record Pack (A : Set) : Set where
  field
    a : A

record Packed {A : Set} (p : Pack A) : Set where
  module PP = Pack p

module Synchronised {A : Set} {p : Pack A} (rel : Packed p) where
  module M = Packed rel
