
module ShouldBePi where

data One : Set where
  one : One

err1 : One
err1 = \x -> x

err2 : One
err2 = one one

err3 : One
err3 x = x

