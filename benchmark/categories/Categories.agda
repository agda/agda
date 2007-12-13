module Categories where

infix 10 _≡_

data _≡_ {A : Set}(a : A) : {B : Set} -> B -> Set where
  refl : a ≡ a

trans : forall {A B C}{a : A}{b : B}{c : C} -> a ≡ b -> b ≡ c -> a ≡ c
trans refl p = p

sym : forall {A B}{a : A}{b : B} -> a ≡ b -> b ≡ a
sym refl = refl

resp : forall {A}{B : A -> Set}{a a' : A} ->
       (f : (a : A) -> B a) -> a ≡ a' -> f a ≡ f a'
resp f refl = refl

record Cat : Set1 where
  field Obj : Set
        Hom : Obj -> Obj -> Set
        id : forall X -> Hom X X
        _○_ : forall {X Y Z} -> Hom Y Z -> Hom X Y -> Hom X Z
        idl : forall {X Y}{f : Hom X Y} -> id Y ○ f ≡ f
        idr : forall {X Y}{f : Hom X Y} -> f ○ id X ≡ f
        assoc : forall {W X Y Z}{f : Hom W X}{g : Hom X Y}{h : Hom Y Z} ->
                (h ○ g) ○ f ≡ h ○ (g ○ f)

open Cat

record Functor (C D : Cat) : Set where
  field Fun : Obj C -> Obj D
        map : forall {X Y} -> (Hom C X Y) -> Hom D (Fun X) (Fun Y)
        mapid : forall {X} -> map (id C X) ≡ id D (Fun X)
        map○ : forall {X Y Z}{f : Hom C X Y}{g : Hom C Y Z} -> 
               map (_○_ C g f) ≡ _○_ D (map g) (map f)

open Functor

idF : forall C -> Functor C C
idF C = record {Fun = \x -> x; map = \x -> x; mapid = refl; map○ = refl}

_•_ : forall {C D E} -> Functor D E -> Functor C D -> Functor C E
F • G = record {Fun = \X -> Fun F (Fun G X);
                 map = \f -> map F (map G f);
                 mapid = trans (resp (\x -> map F x) (mapid G)) (mapid F);
                 map○ = trans (resp (\x -> map F x) (map○ G)) (map○ F)} 

record Nat {C D : Cat} (F G : Functor C D) : Set where
  field η : (X : Obj C) -> Hom D (Fun F X) (Fun G X)
        law : {X Y : Obj C}{f : Hom C X Y} -> 
              _○_ D (η Y) (map F f) ≡ _○_ D (map G f) (η X)

open Nat

_▪_ : forall {C D : Cat}{F G H : Functor C D} -> Nat G H -> Nat F G -> Nat F H
_▪_ {D = D} A B = 
  record {
    η = \X -> _○_ D (η A X) (η B X);
    law = \{X}{Y} ->
      trans (assoc D) 
            (trans (resp (\f -> _○_ D (η A Y) f) (law B))
                   (trans (sym (assoc D))
                          (trans (resp (\g -> _○_ D g (η B X)) (law A)) 
                                 (assoc D))))
  }

