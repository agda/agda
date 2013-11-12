{-# OPTIONS --copatterns #-}

module Issue950a where

postulate
  A : Set

record R : Set where
  field
    x : A

record S : Set where
  field
    y : A

open R

f : A
x f = ?

-- Bad error:

-- Arguments left we cannot split on. TODO: better error message
-- when checking that the clause x f = ? has type A

-- Better error:

-- Cannot eliminate type A with projection pattern x
-- when checking that the clause x f = ? has type A
