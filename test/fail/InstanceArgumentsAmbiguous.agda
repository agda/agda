module InstanceArgumentsAmbiguous where

postulate A B : Set
          f : {{a : A}} → B
          instance a₁ a₂ : A

test : B
test = f
