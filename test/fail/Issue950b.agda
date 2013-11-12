{-# OPTIONS --copatterns #-}

module Issue950b where

postulate
  A : Set

record R : Set where
  field
    x : A

record S : Set where
  field
    y : A

open R

f : ?
x f = ?

-- Good error:

-- Cannot eliminate type ?0 with projection pattern x
-- when checking that the clause x f = ? has type ?0
