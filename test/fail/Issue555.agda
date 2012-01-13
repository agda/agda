-- Andreas, 2012-01-13, error reported by Rob Simmons
module Issue555 where

data Exp : Set
data Exp Γ where -- internal error

