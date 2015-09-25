module Negative2 where

data Tree (A : Set) : Set where
    leaf : Tree A
    node : (A -> Tree A) -> Tree A

data Bad : Set where
    bad : Tree Bad -> Bad

