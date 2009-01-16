module PostulateAndCorecursion where

codata C : Set where

x : C
x ~ y
  where
  postulate y : C
