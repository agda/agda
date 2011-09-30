-- Abstract constructors
module Issue476c where

module M where
  data D : Set

  abstract
    data D where
      c : D

x : M.D
x = M.c