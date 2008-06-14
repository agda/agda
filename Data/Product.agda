------------------------------------------------------------------------
-- Products
------------------------------------------------------------------------

module Data.Product where

open import Data.Function
open import Relation.Nullary.Core

infixr 4 _,_
infixr 2 _×_ _-×-_ _-,-_

------------------------------------------------------------------------
-- Definition

data Σ (a : Set) (b : a -> Set) : Set where
  _,_ : (x : a) -> b x -> Σ a b

∃ : {a : Set} -> (a -> Set) -> Set
∃ = Σ _

∄ : {a : Set} -> (a -> Set) -> Set
∄ P = ¬ ∃ P

_×_ : (a b : Set) -> Set
a × b = Σ a (\_ -> b)

------------------------------------------------------------------------
-- Functions

proj₁ : forall {a b} -> Σ a b -> a
proj₁ (x , y) = x

proj₂ : forall {a b} -> (p : Σ a b) -> b (proj₁ p)
proj₂ (x , y) = y

<_,_> :  {a b c : Set}
      -> (a -> b) -> (a -> c) -> (a -> b × c)
< f , g > x = (f x , g x)

map-× :  {a b c d : Set}
      -> (a -> c) -> (b -> d) -> (a × b -> c × d)
map-× f g = < f ∘ proj₁ , g ∘ proj₂ >

swap : forall {a b} -> a × b -> b × a
swap = < proj₂ , proj₁ >

_-×-_ :  {a b : Set}
       -> (a -> b -> Set) -> (a -> b -> Set) -> (a -> b -> Set)
f -×- g = f -[ _×_ ]₁- g

_-,-_ :  {a b c d : Set}
      -> (a -> b -> c) -> (a -> b -> d) -> (a -> b -> c × d)
f -,- g = f -[ _,_ ]- g

Σ-curry :  {a : Set} {b : a -> Set} {c : Σ a b -> Set}
       -> ((p : Σ a b) -> c p)
       -> ((x : a) -> (y : b x) -> c (x , y))
Σ-curry f x y = f (x , y)

Σ-uncurry :  {a : Set} {b : a -> Set} {c : Σ a b -> Set}
          -> ((x : a) -> (y : b x) -> c (x , y))
          -> ((p : Σ a b) -> c p)
Σ-uncurry f (p₁ , p₂) = f p₁ p₂

curry : {a b c : Set} -> (a × b -> c) -> (a -> b -> c)
curry = Σ-curry

uncurry : {a b c : Set} -> (a -> b -> c) -> (a × b -> c)
uncurry = Σ-uncurry

zip-Σ : forall {A B C P Q R} ->
        (_•_ : A -> B -> C) ->
        (forall {x y} -> P x -> Q y -> R (x • y)) ->
        Σ A P -> Σ B Q -> Σ C R
zip-Σ _•_ _○_ (x , y) (u , v) = (x • u , y ○ v)

map-Σ : forall {A B P Q}
        -> (f : A -> B) -> (forall {x} -> P x -> Q (f x))
        -> Σ A P -> Σ B Q
map-Σ f g (x , y) = (f x , g y)

map-Σ₂ : forall {a P Q} -> (forall {x} -> P x -> Q x) -> Σ a P -> Σ a Q
map-Σ₂ f (x , y) = (x , f y)
