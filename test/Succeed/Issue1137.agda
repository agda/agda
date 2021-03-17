-- We issue a warning for termination pragmas inside `where` clauses.

module Issue1137 where

postulate
  A : Set
  a : A

foo : A
foo = bar
  where
  {-# TERMINATING #-}
  bar : A
  bar = a
