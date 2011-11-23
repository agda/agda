module CoPatWith where

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A -> Maybe A

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

record CoList (A : Set) : Set where
  constructor inn
  field
    out : Maybe (A × CoList A)

open CoList

module With where

  map : {A B : Set}(f : A -> B)(l : CoList A) -> CoList B
  out (map f l) with out l
  out (map f l) | nothing = nothing
  out (map f l) | just (a , as) = just (f a , map f as)

module NoWith where

  map : {A B : Set}(f : A -> B)(l : CoList A) -> CoList B
  out (map {A = A}{B = B} f l) = map' f l (out l)
    where outmap : (f : A -> B)(l : CoList A)(outl : Maybe (A × CoList A)) -> Maybe (B × CoList B)
          outmap f l nothing = nothing
          outmap f l (just (a , as)) = just (f a , map f as) 

module With2 where

  map : {A B : Set}(f : A -> B)(l : CoList A) -> CoList B
  out (map f (inn l)) with l
  out (map f (inn .nothing))         | nothing       = nothing
  out (map f (inn .(just (a , as)))) | just (a , as) = just (f a , map f as)

module NoWith2 where

  map : {A B : Set}(f : A -> B)(l : CoList A) -> CoList B
  out (map {A = A}{B = B} f l) = map' f l (out l)
    where outmap : (f : A -> B)(l : CoList A)(outl : Maybe (A × CoList A)) -> Maybe (B × CoList B)
          outmap f (inn .nothing)         nothing         = nothing
          outmap f (inn .(just (a , as))) (just (a , as)) = just (f a , map f as) 
