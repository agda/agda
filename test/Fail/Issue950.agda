{-# OPTIONS --copatterns #-}

module Issue950 where

postulate
  A : Set

record R : Set where
  field
    x : A

record S : Set where
  field
    y : A

open R

f : S
x f = ?

-- Bad error:

-- Arguments left we cannot split on. TODO: better error message
-- when checking that the clause x f = ? has type S

-- Better error:

-- Cannot eliminate type S with projection pattern x
-- when checking that the clause x f = ? has type S
