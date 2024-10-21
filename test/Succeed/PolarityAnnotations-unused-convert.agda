{-# OPTIONS --polarity #-}

module _ where

open import Agda.Builtin.Equality

postulate A : Set
postulate f : @unused A → A

eq : {x y : A} → f x ≡ f y
eq = refl
