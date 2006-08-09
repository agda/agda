
module UnequalTypes where

data One  : Set where one : One

err1 : One -> One
err1 = one

err2 : (One -> One) -> One
err2 = \(x:One) -> one

