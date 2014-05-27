module Pruning where

le2 : {B : Set} -> (A : Set) -> A -> (C : Set) -> C -> (A -> C -> B) -> B
le2 _ x _ y f = f x y

test : le2 Set _ (Set -> Set) _ (\ H -> (\M -> (z : Set) -> H == M z))
test z = refl 

{-
let : {B : Set} -> (A : Set) -> A -> (A -> B) -> B
let A x f = f x

test : let Set _ (\ H -> let (Set -> Set) _ (\ M -> (z : Set) -> H == M z))
test z = refl 
-}