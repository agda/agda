{-# OPTIONS --type-in-type #-}
module Record where

open import Prelude

record Sigma (A : Set)(B : A -> Set) : Set
record Sigma A B where
  constructor pair
  field
    fst : A
    snd : B fst

open Sigma

data Unit : Set
data Unit where
  tt : Unit

Cat : Set
Cat =
  Sigma Set                                                  (\ Obj ->
  Sigma (Obj -> Obj -> Set)                                  (\ Hom ->
  Sigma ((X : _) -> Hom X X)                                 (\ id ->
  Sigma ((X Y Z : _) -> Hom Y Z -> Hom X Y -> Hom X Z)       (\ comp ->
  Sigma ((X Y : _)(f : Hom X Y) -> comp _ _ _ (id Y) f == f) (\ idl ->
  Sigma ((X Y : _)(f : Hom X Y) -> comp _ _ _ f (id X) == f) (\ idr ->
  Sigma ((W X Y Z : _)
         (f : Hom W X)(g : Hom X Y)(h : Hom Y Z) ->
           comp _ _ _ (comp _ _ _ h g) f ==
           comp _ _ _ h (comp _ _ _ g f))                    (\ assoc ->
  Unit)))))))

Obj : (C : Cat) -> Set
Obj C = fst C

Hom : (C : Cat) -> Obj C -> Obj C -> Set
Hom C = fst (snd C)

id : (C : Cat) -> (X : _) -> Hom C X X
id C = fst (snd (snd C))

comp : (C : Cat) -> (X Y Z : _) -> Hom C Y Z -> Hom C X Y -> Hom C X Z
comp C = fst (snd (snd (snd C)))

idl : (C : Cat) -> (X Y : _)(f : Hom C X Y) ->
      comp C _ _ _ (id C Y) f == f
idl C = fst (snd (snd (snd (snd C))))

idr : (C : Cat) -> (X Y : _)(f : Hom C X Y) ->
      comp C _ _ _ f (id C X) == f
idr C = fst (snd (snd (snd (snd (snd C)))))

assoc : (C : Cat) ->
        (W X Y Z : _) (f : Hom C W X)(g : Hom C X Y)(h : Hom C Y Z) ->
        comp C _ _ _ (comp C _ _ _ h g) f ==
        comp C _ _ _ h (comp C _ _ _ g f)
assoc C = fst (snd (snd (snd (snd (snd (snd C))))))
