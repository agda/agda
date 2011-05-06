module InstanceArgumentsAmbiguous where

postulate A B : Set
          f : {{a : A}} → B
          a₁ a₂ : A

test : B
test = f
