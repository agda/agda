{-# OPTIONS --cubical --with-K --safe #-}
module _ where

open import Agda.Builtin.Equality

uip : ∀ {a} {A : Set a} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl
