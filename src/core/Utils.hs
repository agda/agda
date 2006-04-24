
module Utils where

import Control.Monad

f <$> m = liftM f m
f <*> m = ap f m
