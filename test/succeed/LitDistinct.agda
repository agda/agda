
module LitDistinct where

postulate String : Set
{-# BUILTIN STRING String #-}

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data False : Set where

foo : "bar" == "baz" -> False
foo ()

