-- Andreas, 2013-02-26
module Issue799a where

data D (A : Set1) : Set where
  d : D A

x : D Set
x = d {A = _} -- correct parameter name

y : D Set
y = d {B = _} -- wrong parameter name, should give error
