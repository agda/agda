
module UnequalSorts where

data One  : Set  where one : One
data One' : Set1 where one' : One'

err : One
err = one'

