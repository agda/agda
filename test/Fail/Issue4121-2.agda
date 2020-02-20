module _ where

module M where

  data D : Set where
    c : D

  pattern c′ = c

open M hiding (c′)

x : D
x = c′
