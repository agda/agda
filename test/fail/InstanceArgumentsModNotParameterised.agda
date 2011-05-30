module InstanceArgumentsModNotParameterised where

postulate A : Set
          a : A

record B : Set where
  field bA : A

b : B
b = record {bA = a}

module C = B b

open C {{...}}
