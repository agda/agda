-- {-# OPTIONS -v tc.term.con:100 #-}
module Issue799 where

data D : Set where
  d : D

x : D
x = d {_} {_} {interesting-argument = _} {_} {_} {_}
  -- should fail
