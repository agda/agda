module InstanceArgumentsNotFound where

postulate A B : Set
          f : {{a : A}} → B

test : B
test = f
