------------------------------------------------------------------------
-- Products
------------------------------------------------------------------------

module Data.Product where

open import Data.Function
open import Relation.Nullary.Core

infixr 4 _,_
infix  4 ,_
infixr 2 _×_ _-×-_ _-,-_

------------------------------------------------------------------------
-- Definition

data Σ (A : Set) (B : A -> Set) : Set where
  _,_ : (x : A) (y : B x) -> Σ A B

∃ : {A : Set} -> (A -> Set) -> Set
∃ = Σ _

∄ : {A : Set} -> (A -> Set) -> Set
∄ P = ¬ ∃ P

∃₂ : {A B : Set} (C : A -> B -> Set) -> Set
∃₂ C = ∃ \a -> ∃ \b -> C a b

_×_ : (A B : Set) -> Set
A × B = Σ A (\_ -> B)

------------------------------------------------------------------------
-- Functions

-- Sometimes the first component can be inferred.

,_ : forall {A} {B : A -> Set} {x} -> B x -> ∃ B
, y = _ , y

proj₁ : forall {A B} -> Σ A B -> A
proj₁ (x , y) = x

proj₂ : forall {A B} -> (p : Σ A B) -> B (proj₁ p)
proj₂ (x , y) = y

<_,_> : {A B C : Set} ->
        (A -> B) -> (A -> C) -> (A -> B × C)
< f , g > x = (f x , g x)

map-× : {A B C D : Set} ->
        (A -> C) -> (B -> D) -> (A × B -> C × D)
map-× f g = < f ∘ proj₁ , g ∘ proj₂ >

swap : forall {A B} -> A × B -> B × A
swap = < proj₂ , proj₁ >

_-×-_ : {A B : Set} ->
        (A -> B -> Set) -> (A -> B -> Set) -> (A -> B -> Set)
f -×- g = f -[ _×_ ]₁- g

_-,-_ : {A B C D : Set} ->
        (A -> B -> C) -> (A -> B -> D) -> (A -> B -> C × D)
f -,- g = f -[ _,_ ]- g

Σ-curry : {A : Set} {B : A -> Set} {C : Σ A B -> Set} ->
          ((p : Σ A B) -> C p) ->
          ((x : A) -> (y : B x) -> C (x , y))
Σ-curry f x y = f (x , y)

Σ-uncurry : {A : Set} {B : A -> Set} {C : Σ A B -> Set} ->
            ((x : A) -> (y : B x) -> C (x , y)) ->
            ((p : Σ A B) -> C p)
Σ-uncurry f (p₁ , p₂) = f p₁ p₂

curry : {A B C : Set} -> (A × B -> C) -> (A -> B -> C)
curry = Σ-curry

uncurry : {A B C : Set} -> (A -> B -> C) -> (A × B -> C)
uncurry = Σ-uncurry

zip-Σ : forall {A B C P Q R} ->
        (_∙_ : A -> B -> C) ->
        (forall {x y} -> P x -> Q y -> R (x ∙ y)) ->
        Σ A P -> Σ B Q -> Σ C R
zip-Σ _∙_ _∘_ (x , y) (u , v) = (x ∙ u , y ∘ v)

map-Σ : forall {A B P Q} ->
        (f : A -> B) -> (forall {x} -> P x -> Q (f x)) ->
        Σ A P -> Σ B Q
map-Σ f g (x , y) = (f x , g y)

map-Σ₂ : forall {A} {P Q : A -> Set} ->
         (forall {x} -> P x -> Q x) -> ∃ P -> ∃ Q
map-Σ₂ = map-Σ id
