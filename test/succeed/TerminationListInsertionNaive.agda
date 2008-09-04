module TerminationListInsertionNaive where

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

infixr 50 _::_

-- non-deterministic choice
postulate
  _⊕_ : {A : Set} -> A -> A -> A  
infixl 10 _⊕_

-- a funny formulation of insert
-- insert (a :: l)  inserts a into l 
--
-- this example cannot be handled with subpatterns
-- it is done with structured orders
-- could also be done with sized types

insert : {A : Set} -> List A -> List A
insert [] = []
insert (a :: []) = a :: []
insert (a :: b :: bs) = a :: b :: bs ⊕        -- case a <= b 
                        b :: insert (a :: bs) -- case a > b


-- list flattening
-- termination using structured orders
flat : {A : Set} -> List (List A) -> List A
flat [] = []
flat ([] :: ll) = flat ll
flat ((x :: l) :: ll) = x :: flat (l :: ll)

{- generates two recursive calls with the following call matrices

  
      [] :: ll         (x :: l)   ll            
                                       
  ll  <            l   <          .          
                   ll  .          =

during composition, the second is collapsed to =, so the call graph is
already complete.  Both matrices are idempotent and contain a strictly
decreasing argument.  

It could also be done with sized types; lexicographic in (i,j)
with type

  flat : {A : Set} -> (1 + Listʲ A × List^i (List^∞ A)) -> List^∞ A


-}
