{-# OPTIONS --polarity #-}

module UnequalPolarity where

f : (@++ A : Set) → Set
f X = X

g : Set → Set
g = f
