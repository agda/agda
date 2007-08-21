
module Problem4 where

infixr 40 _::_

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

-- 4.1

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

infixr 40 _++_

_++_ : {A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

-- 4.2

infixr 40 _▹_

data All {A : Set}(P : A -> Set) : List A -> Set where
  ∅   : All P []
  _▹_ : {x : A} -> P x -> {xs : List A} -> All P xs -> All P (x :: xs)

-- 4.3

data Some {A : Set}(P : A -> Set) : List A -> Set where
  hd : {x : A} -> P x -> {xs : List A}   -> Some P (x :: xs)
  tl : {x : A}{xs : List A} -> Some P xs -> Some P (x :: xs)

-- 4.4

-- We need composition at a higher universe here.

_∘¹_ : {A B : Set}{C : B -> Set1}(f : (x : B) -> C x)
       (g : A -> B)(x : A) -> C (g x)
(f ∘¹ g) x = f (g x)

-- You might have to give f explictly when applying this theorem.

all-map : {A B : Set}{P : A -> Set}{Q : B -> Set}{f : A -> B}{xs : List A} ->
          ({x : A} -> P x -> Q (f x)) ->
          All P xs -> All Q (map f xs)
all-map h ∅        = ∅
all-map h (p ▹ ps) = h p ▹ all-map h ps

all-++ : {A : Set}{P : A -> Set}{xs ys : List A} ->
         All P xs -> All P ys -> All P (xs ++ ys)
all-++ ∅        qs = qs
all-++ (p ▹ ps) qs = p ▹ (all-++ ps qs)

some-map : {A B : Set}{P : A -> Set}{Q : B -> Set}{f : A -> B}{xs : List A} ->
           ({x : A} -> P x -> Q (f x)) ->
           Some P xs -> Some Q (map f xs)
some-map h (hd p)  = hd (h p)
some-map h (tl ps) = tl (some-map h ps)

some-++-left : {A : Set}{P : A -> Set}{xs ys : List A} ->
               Some P xs -> Some P (xs ++ ys)
some-++-left (hd p)  = hd p
some-++-left (tl ps) = tl (some-++-left ps)

-- Here we can't expect to infer xs, so we make it explicit

some-++-right : {A : Set}{P : A -> Set}(xs : List A){ys : List A} ->
               Some P ys -> Some P (xs ++ ys)
some-++-right []        p = p
some-++-right (x :: xs) p = tl (some-++-right xs p)

-- 4.5

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

_∈_ : {A : Set} -> A -> List A -> Set
x ∈ xs = Some (_==_ x) xs

-- 4.6

record True : Set where

tt : True
tt = record {}

Nat  = List True

zero : Nat
zero = []

suc : Nat -> Nat
suc n = tt :: n

Vec : Set -> Nat -> Set
Vec A n = All (\_ -> A) n

Fin : Nat -> Set
Fin n = Some (\_ -> True) n

-- 4.7

infixr 5 _,_

data _×_ (A : Set)(B : A -> Set) : Set where
  _,_ : (x : A) -> B x -> A × B

_∧_ : Set -> Set -> Set
A ∧ B = A × (\_ -> B)

_!_ : {A : Set}{P : A -> Set}{Q : A -> Set}{xs : List A} ->
      All P xs -> Some Q xs -> A × (\z -> P z ∧ Q z)
∅ ! ()
(p ▹ ps) ! hd q = (_ , p , q)
(p ▹ ps) ! tl q = ps ! q

-- 4.8

data False : Set where

¬_ : Set -> Set
¬ A = A -> False

data _∨_ (A B : Set) : Set where
  inl : A -> A ∨ B
  inr : B -> A ∨ B

data Bool : Set where
  true  : Bool
  false : Bool

data IsTrue : Bool -> Set where
  isTrue : IsTrue true

Holds : {A : Set} -> (A -> Bool) -> A -> Set
Holds p x = IsTrue (p x)

false-isn't-true : ¬ IsTrue false
false-isn't-true ()

decide : {A : Set}(p : A -> Bool)(x : A) ->
         Holds p x ∨ ¬ Holds p x
decide p x with p x
...        | true  = inl isTrue
...        | false = inr false-isn't-true

all : {A : Set}(p : A -> Bool)(xs : List A) ->
      All (Holds p) xs ∨ Some (\x -> ¬ Holds p x) xs
all p [] = inl ∅
all p (x :: xs) with decide p x
... | inr npx = inr (hd npx)
... | inl px  with all p xs
...   | inr npxs = inr (tl npxs)
...   | inl pxs  = inl (px ▹ pxs)
