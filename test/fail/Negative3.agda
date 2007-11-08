module Negative3 where

data Mu (F : Set -> Set) : Set where
    inn : F (Mu F) -> Mu F


