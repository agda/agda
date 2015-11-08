
-- Pattern matching on a (decidably) empty type allows you to omit the
-- right-hand side.
module AbsurdPattern where

data Empty : Set where

elim-Empty : {A : Set} -> Empty -> A
elim-Empty ()

