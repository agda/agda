{-# OPTIONS --without-K #-}
module Common.List where

open import Agda.Builtin.List public
open import Common.Nat

infixr 5 _++_

_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map _ []       = []
map f (x ∷ xs) = f x ∷ map f xs

length : ∀ {a} {A : Set a} → List A → Nat
length []       = 0
length (x ∷ xs) = 1 + length xs
