
module All where

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f z [] = z
foldr f z (x :: xs) = f x (foldr f z xs)

data All {A : Set}(P : A -> Set) : List A -> Set where
  ∅   : All P []
  _▹_ : {x : A}{xs : List A} -> P x -> All P xs -> All P (x :: xs)

data Some {A : Set}(P : A -> Set) : List A -> Set where
  hd : {x : A}{xs : List A} -> P x       -> Some P (x :: xs)
  tl : {x : A}{xs : List A} -> Some P xs -> Some P (x :: xs)

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

_∈_ : {A : Set} -> A -> List A -> Set
x ∈ xs = Some (_==_ x) xs

infixr 40 _,_

data _×_ (A : Set)(B : A -> Set) : Set where
  _,_ : (x : A) -> B x -> A × B

_∧_ : (A B : Set) -> Set
A ∧ B = A × \_ -> B

_!_ : {A : Set}{P : A -> Set}{Q : A -> Set}{xs : List A} ->
      All P xs -> Some Q xs -> A × (\x -> P x ∧ Q x)
ε ! ()
(p ▹ ps) ! hd q = _ , (p , q)
(p ▹ ps) ! tl q = ps ! q
