{-
   Checking that nesting invertible functions works properly. In this example
   we should get

    El2 α = B         {reduces to}
    El1 (embed α) = B {simplifies by invertibility to}
    embed α = b       {simplifies by invertibility to}
    α = b
-}
module NestedInj where

data A : Set where
  theA : A

data B : Set where
  theB : B

data U1 : Set where
  a : U1
  b : U1

data U2 : Set where
  b : U2

El1 : U1 -> Set
El1 a = A
El1 b = B

embed : U2 -> U1
embed b = b

El2 : U2 -> Set
El2 c = El1 (embed c)

f1 : {c : U1} -> El1 c -> El1 c
f1 {a} theA = theA
f1 {b} theB = theB

f2 : {c : U2} -> El2 c -> El2 c
f2 x = f1 x

test : B
test = f2 theB
