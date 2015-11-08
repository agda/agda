module UnderscoresAsDataParam where

data List (A : Set) : Set where
  nil  : List _
  cons : A -> List A -> List _
