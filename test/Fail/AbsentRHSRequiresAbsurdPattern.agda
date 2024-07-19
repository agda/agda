-- You can omit the right hand side if you pattern match on an empty type. But
-- you have to do the matching.
module AbsentRHSRequiresAbsurdPattern where

data Zero : Set where

good : {A : Set} -> Zero -> A
good ()

bad : {A : Set} -> Zero -> A
bad h
