{-# OPTIONS --cubical #-}
module Issue3660 where

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path

module _ where

data D (A : Set) : Set where
  c : A → D A
  path : (x : A) → c x ≡ c x

map : {A B : Set} → (A → B) → D A → D B
map f (c x) = c (f x)
map f (path x i) = path (f x) {!!}
