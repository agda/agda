-- Andreas, 2013-02-18 recursive meta occurrence no longer throws error
{-
{-# OPTIONS --allow-unsolved-metas #-}
-- The option is supplied to force a real error to pass the regression test.
-}
module MetaOccursInItself where

data List (A : Set) : Set where
  nil  : List A
  _::_ : A -> List A -> List A

data One : Set where one : One

postulate
  f : (A : Set) -> (A -> List A) -> One

err : One
err = f _ (\x -> x)
