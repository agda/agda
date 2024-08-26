{-# OPTIONS --experimental-irrelevance #-}

record ShapeIrrelevant (A : Set) : Set where
  constructor [_]
  field
    ..! : A

open ShapeIrrelevant

map-ns : {A B : Set} (f : A → B) → ShapeIrrelevant A → ShapeIrrelevant B
map-ns f [ x ] = [ f x ]

open import Agda.Builtin.Nat

data Vec (A : Set) : ShapeIrrelevant Nat → Set where
  []  : Vec A [ 0 ]
  _∷_ : .{n : Nat} → A → Vec A [ n ] → Vec A [ suc n ]

map : ∀ {A B} .{n} (f : A → B) → Vec A [ n ] → Vec B [ n ]
map f [] = []
map f (x ∷ xs) = (f x) ∷ (map f xs)
