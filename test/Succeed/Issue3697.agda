{-# OPTIONS --type-in-type #-}

open import Agda.Primitive using (Setω)

-- No panic should be triggered

data A : Setω where

record B' : Set where
  field
    theA : A

data B : Set where
  b : A → B

data C : Set where
  c : Setω → C


data C' : Setω where
  c : Setω → C'


record C'' : Setω where
  field
    theSet : Setω
    thefield : theSet
