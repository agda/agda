-- There was a bug where the arguments to a let function got reversed.
module LetLHS where

f : {A B : Set} -> A -> B -> A
f {A}{B} = let const : A -> B -> A 
               const x y = x
           in const
