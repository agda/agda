{-# OPTIONS --copatterns #-}
module Tree where

data Bool : Set where
  true false : Bool

record Tree (A : Set) : Set where
  field 
    label : A
    child : Bool -> Tree A
open Tree

-- corecursive function defined by copattern matching 
alternate : {A : Set}(a b : A) -> Tree A
-- deep copatterns:
label (child (alternate a b) false)       = b
child (child (alternate a b) false) true  = alternate a b
child (child (alternate a b) false) false = alternate a b
-- shallow copatterns
child {A = A} (alternate a b) true = alternate b a
label {A = A} (alternate a b)      = a

{- Delivers an infinite tree

                 a
            b        b
          a   a    a   a
         b b b b  b b b b 
               ...
-}

infixr 5 _::_

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

collect : List Bool -> {A : Set} -> Tree A -> List A
collect []       t = []
collect (b :: l) t = label t :: collect l (child t b)

test : List Bool 
test = collect (true :: true :: true :: []) (alternate true false)
-- should give true :: false : true :: []
 