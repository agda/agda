
module Utils where

infixl 8 `on`

f `on` g = \x y -> f (g x) (g y)
