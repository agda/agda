{-

          Types Summer School 2007

                 Bertinoro
             Aug 19 - 31, 2007


                   Agda

                Ulf Norell

-}

module Filter where

open import Nat

data Bool : Set where
  false : Bool
  true  : Bool

infixr 40 _::_

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p [] = []
filter p (x :: xs) with p x
filter p (x :: xs) | true  = x :: filter p xs
filter p (x :: xs) | false = filter p xs

infix 20 _⊆_

data _⊆_ {A : Set} : List A -> List A -> Set where
  stop : [] ⊆ []
  drop : forall {xs y ys} -> xs ⊆ ys -> xs ⊆ y :: ys
  keep : forall {x xs ys} -> xs ⊆ ys -> x :: xs ⊆ x :: ys

subset : {A : Set}(p : A -> Bool)(xs : List A) -> filter p xs ⊆ xs
subset p []        = stop
subset p (x :: xs) with p x
... | true = keep (subset p xs) 
... | false = drop (subset p xs) 

{-
subset p (x :: xs) with p x
subset p (x :: xs) | true  = keep (subset p xs)
subset p (x :: xs) | false = drop (subset p xs)
-}
