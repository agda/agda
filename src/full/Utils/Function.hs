
module Utils.Function where

on :: (a -> a -> b) -> (c -> a) -> c -> c -> b
on f g x y = f (g x) (g y)

