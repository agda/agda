{-# OPTIONS --safe #-}

A : Set

record B : Set

data C : Set

D : Set
D = Set
-- should throw Set₁ != Set despite earlier missing definitions error
