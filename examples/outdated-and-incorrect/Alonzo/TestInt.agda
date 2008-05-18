module TestInt where

open import PreludeInt
open import PreludeShow

mainS = showInt result where
  result = (mod (((int 2) + (int 2)) * (int 5)) (int 3))