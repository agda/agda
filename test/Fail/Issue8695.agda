{-# OPTIONS --cubical --safe #-}

module Issue8695 where

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Equality renaming (_≡_ to Id; refl to reflId)

data ⊥ : Set where

data A : Set
data B : Set

data A where
  wrapA : B → A

data B where
  b0  : B
  inB : A → B
  e   : (a : A) → inB (wrapA (inB a)) ≡ inB a

f : (x : A) → Id x (wrapA (inB x)) → ⊥
f x ()

X : A
X = wrapA (inB (wrapA b0))

boom : ⊥
boom = f X (primTransp (λ i → Id X (wrapA (e (wrapA b0) (primINeg i)))) i0 reflId)
