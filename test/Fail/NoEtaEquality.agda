-- Andreas, 2016-09-20 test whether --no-eta-equality is respected

{-# OPTIONS --no-eta-equality #-}

record ⊤ : Set where

test : ⊤
test = _ -- should remain unsolved
