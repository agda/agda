
module Utils where

import Data.List

on f g x y = f (g x) (g y)

(f -*- g) (x, y) = (f x, g y)

intercalate x = concat . intersperse x
