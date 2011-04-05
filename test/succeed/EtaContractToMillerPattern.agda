-- Andreas, 2011-04-05
module EtaContractToMillerPattern where

data _==_ {A : Set}(a : A) : A -> Set where
  refl : a == a

record Prod (A B : Set) : Set where
  constructor _,_
  field fst : A
        snd : B
open Prod

postulate A B C : Set

test : let X : (Prod A B -> C) -> (Prod A B -> C)
           X = _
       in (x : Prod A B -> C) -> 
            X (\ z -> x (fst z , snd z)) == x
test x = refl 
-- eta contracts unification problem to  X x = x