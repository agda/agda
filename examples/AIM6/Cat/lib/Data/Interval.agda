
module Data.Interval where

data Interval (A : Set) : Set where
  [_▻_] : A -> A -> Interval A

lowerBound : {A : Set} -> Interval A -> A
lowerBound [ l ▻ u ] = l

upperBound : {A : Set} -> Interval A -> A
upperBound [ l ▻ u ] = u

