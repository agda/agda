
module Issue892 where

data D : Set where
  d : D

module I where
  i : D
  i = d

module M0 (X : Set) where
  module M1 where
    h : D
    h = d
  module M2 where
    open M1 public
    open I public

module M = M0 D

good : D
good = M.M1.h

bad : D
bad = M.M2.h
