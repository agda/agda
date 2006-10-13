
module Prelude where

id : {A : Set} -> A -> A
id x = x

infixr 90 _∘_
_∘_ : {A, B, C : Set} -> (B -> C) -> (A -> B) -> A -> C
(f ∘ g) x = f (g x)

typeOf : {A : Set} -> A -> Set
typeOf {A} _ = A

