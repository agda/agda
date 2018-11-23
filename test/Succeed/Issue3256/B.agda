{-# OPTIONS --allow-unsolved-metas #-}

module Issue3256.B where

f : (a : Set) -> a -> a
f a y = {!!} y
