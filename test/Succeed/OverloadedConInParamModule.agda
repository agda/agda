
module OverloadedConInParamModule where

data A : Set where

module M (X : Set) where
  data B : Set where
    c : B

  data C : Set where
    c : C

open M A

f : B
f = c
