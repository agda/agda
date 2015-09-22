-- Occurs when different mixfix operators use similar names.
module Issue147a where

postulate
  X  : Set
  f  : X -> X
  f_ : X -> X

bad : X -> X
bad x = f x

