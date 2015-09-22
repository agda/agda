module AbstractBlockInLet where

postulate
  A : Set
  a : A

test = let abstract
             x = a
             y = x
       in y
