module Negative3 where

data Mu (F : Set -> Set) : Set where
    in : F (Mu F) -> Mu F


