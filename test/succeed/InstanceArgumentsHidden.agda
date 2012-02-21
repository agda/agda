module InstanceArgumentsHidden where

record ⊤ : Set where

-- check that the instance argument resolution takes into account
-- instances which take hidden arguments to be of the correct type.
postulate A1 A2 B : Set
          f1 : {{a : A1}} → B
          f2 : {{a : A2}} → B
          inst1 : {_ : ⊤} → A1

checkProperty : ⊤ → Set
checkProperty _ = ⊤

postulate inst2 : {a : ⊤} → {_ : checkProperty a} → A2

test1 = f1
test2 = f2
