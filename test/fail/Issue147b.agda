-- Occurs when different mixfix patterns use similar names.
module Issue147b where

data X : Set where
  f  : X -> X
  f_ : X -> X
  x  : X

bad : X -> X
bad (f x) = x
bad _     = x
