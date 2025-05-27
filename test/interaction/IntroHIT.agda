{-# OPTIONS --cubical #-}
module IntroHIT where

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical

data Tr (A : Set) : Set where
  inc : A → Tr A
  squash : ∀ x y → x ≡ y

test : {A : Set} (x : A) → Tr A
test x = {! !}
