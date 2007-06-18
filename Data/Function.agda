------------------------------------------------------------------------
-- Simple combinators working solely on and with functions
------------------------------------------------------------------------

module Data.Function where

infixr 9 _∘_
infixl 1 _on_ _on₁_
infixr 0 _-[_]₁-_ _-[_]-_ _$_

_∘_ : {a b c : Set} -> (b -> c) -> (a -> b) -> (a -> c)
f ∘ g = \x -> f (g x)

id : {a : Set} -> a -> a
id x = x

const : {a b : Set} -> a -> b -> a
const x = \_ -> x

flip : {a b c : Set} -> (a -> b -> c) -> (b -> a -> c)
flip f = \x y -> f y x

flip₁ : {a b : Set} -> (a -> b -> Set) -> (b -> a -> Set)
flip₁ f = \x y -> f y x

_$_ : {a : Set} {b : a -> Set} -> ((x : a) -> b x) -> ((x : a) -> b x)
f $ x = f x

_⟨_⟩_ : {a b c : Set} -> a -> (a -> b -> c) -> b -> c
x ⟨ f ⟩ y = f x y

_⟨_⟩₁_ : {a b : Set} -> a -> (a -> b -> Set) -> b -> Set
x ⟨ f ⟩₁ y = f x y

_on_ : {a b c : Set} -> (b -> b -> c) -> (a -> b) -> (a -> a -> c)
_*_ on f = \x y -> f x * f y

_on₁_ :  {a b : Set} {c : Set1}
      -> (b -> b -> c) -> (a -> b) -> (a -> a -> c)
_*_ on₁ f = \x y -> f x * f y

_-[_]-_ :  {a b c d e : Set}
        -> (a -> b -> c) -> (_*_ : c -> d -> e) -> (a -> b -> d)
        -> (a -> b -> e)
f -[ _*_ ]- g = \x y -> f x y * g x y

_-[_]₁-_ :  {a b : Set}
         -> (a -> b -> Set) -> (Set -> Set -> Set) -> (a -> b -> Set)
         -> (a -> b -> Set)
f -[ _*_ ]₁- g = \x y -> f x y * g x y
