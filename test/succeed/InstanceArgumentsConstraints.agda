
module InstanceArgumentsConstraints where

data Bool : Set where
  true false : Bool

postulate A1 A2 B C : Set
          a1 : A1
          a2 : A2
          someF : A1 → C

record Class (R : Bool → Set) : Set where
  field f : (t : Bool) → R t

open Class {{...}}

class1 : Class (λ _ → A1)
class1 = record { f = λ _ → a1 }

class2 : Class (λ _ → A2)
class2 = record { f = λ _ → a2 }

test : C
test = someF (f true)
