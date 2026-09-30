module Issue6374 where

record A : Set where
  constructor c

record B : Set where
  constructor c

a : A
a = {!!} -- C-c C-r does not work
