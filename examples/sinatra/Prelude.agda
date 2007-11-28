
module Prelude where

infixr 50 _,_
infixl 40 _◄_
infix  30 _∈_

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

data List (A : Set) : Set where
  ε   : List A
  _◄_ : List A -> A -> List A

data _∈_ {A : Set}(x : A) : List A -> Set where
  hd : forall {xs}   ->           x ∈ xs ◄ x
  tl : forall {y xs} -> x ∈ xs -> x ∈ xs ◄ y 

data Box {A : Set}(P : A -> Set) : List A -> Set where
  ⟨⟩  : Box P ε
  _◃_ : forall {xs x} -> Box P xs -> P x -> Box P (xs ◄ x)

_!_ : {A : Set}{P : A -> Set}{xs : List A}{x : A} ->
      Box P xs -> x ∈ xs -> P x
⟨⟩      ! ()
(_ ◃ v) ! hd   = v
(ρ ◃ _) ! tl x = ρ ! x

