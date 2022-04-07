{-# OPTIONS --cubical-compatible #-}
-- Issue raised by Martin Escardo 2012-12-13
-- on the Agda list "no longer type checks"
module WithoutKDisjointSum where

open import Common.Equality

data ⊥ : Set where

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

distinct : {A B : Set} (a : A) (b : B) → inl a ≡ inr b → ⊥
distinct a b ()
