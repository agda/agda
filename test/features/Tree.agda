module Tree where

data Bool : Set where
  true false : Bool

record Tree (A : Set) : Set where
  field 
    label : A
    child : Bool -> Tree A

-- corecursive function defined by copattern matching 
alternate : {A : Set}(a b : A) -> Tree A
-- shallow copatterns
child True  (alternate a b) = alternate b a
label       (alternate a b) = a
-- deep copatterns:
label       (child False (alternate a b)) = b
child True  (child False (alternate a b)) = alternate a b
child False (child False (alternate a b)) = alternate a b

{- Delivers an infinite tree

                 a
            b        b
          a   a    a   a
         b b b b  b b b b 
               ...
-}

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

collect : List Bool -> {A : Set} -> Tree A -> List A
collect []       t = []
collect (b :: l) t = label t :: collect l (child t b)

test : List Bool 
test = collect (true :: true :: true :: []) (alternate true false)
-- should give true :: false : true :: []
 