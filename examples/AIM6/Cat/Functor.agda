
module Functor where

open import Category as Cat

record Functor (ℂ ⅅ : Cat) : Set1 where
  field
    F          : Cat.Obj ℂ -> Cat.Obj ⅅ
    map        : {A B : Cat.Obj ℂ} -> Cat._─→_ ℂ A B -> Cat._─→_ ⅅ (F A) (F B)
    mapEq      : {A B : Cat.Obj ℂ}{f g : Cat._─→_ ℂ A B} -> Category._==_ ℂ f g ->
                 Category._==_ ⅅ (map f) (map g)
    mapId      : {A : Cat.Obj ℂ} -> Category._==_ ⅅ (map (Cat.id ℂ {A})) (Cat.id ⅅ)
    mapCompose : {A B C : Cat.Obj ℂ}{f : Cat._─→_ ℂ B C}{g : Cat._─→_ ℂ A B} ->
                 Category._==_ ⅅ (map (Cat._∘_ ℂ f g)) (Cat._∘_ ⅅ (map f) (map g))

