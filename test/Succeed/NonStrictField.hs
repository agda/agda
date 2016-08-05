{-# OPTIONS --experimental-irrelevance #-}

record NonStrict (A : Set) : Set where
  constructor [_]
  field
    ..! : A

open NonStrict

map-ns : {A B : Set} (f : A → B) → NonStrict A → NonStrict B
map-ns f [ x ] = [ f x ]

open import Agda.Builtin.Nat

data Vec (A : Set) : NonStrict Nat → Set where
  []  : Vec A [ 0 ]
  _∷_ : .{n : Nat} → A → Vec A [ n ] → Vec A [ suc n ]

map : ∀ {A B} .{n} (f : A → B) → Vec A [ n ] → Vec B [ n ]
map f [] = []
map f (x ∷ xs) = (f x) ∷ (map f xs)
