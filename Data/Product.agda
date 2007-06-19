------------------------------------------------------------------------
-- Products
------------------------------------------------------------------------

module Data.Product where

open import Data.Function

infixr 4 _,_
infixr 2 _×_ _-×-_ _-,-_

------------------------------------------------------------------------
-- Definition

record Π (a : Set) (b : a -> Set) : Set where
  proj₁ : a
  proj₂ : b proj₁

open Π

_×_ : (a b : Set) -> Set
a × b = Π a (\_ -> b)

------------------------------------------------------------------------
-- Functions

_,_ : forall {a b} -> (x : a) -> b x -> Π a b
x , y = record { proj₁ = x; proj₂ = y }

<_,_> :  {a b c : Set}
      -> (a -> b) -> (a -> c) -> (a -> b × c)
< f , g > x = f x , g x

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

curry :  {a : Set} {b : a -> Set} {c : Π a b -> Set}
      -> ((p : Π a b) -> c p)
      -> ((x : a) -> (y : b x) -> c (x , y))
curry f x y = f (x , y)

uncurry :  {a : Set} {b : a -> Set} {c : Π a b -> Set}
        -> ((x : a) -> (y : b x) -> c (x , y))
        -> ((p : Π a b) -> c p)
uncurry f p = f (proj₁ p) (proj₂ p)
