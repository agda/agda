module DottedConstructor where

data D : Set where
  d : D

f : D
f = .d
