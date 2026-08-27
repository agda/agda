{-# OPTIONS --safe --prop #-}
-- Variant of Issue8694.agda using Prop instead of irrelevance

open import Agda.Builtin.Equality

data ⊥ : Set where

data Squash (A : Set) : Prop where
  squash : A → Squash A

data T : Set where
  w : T
  t : Squash T → T

f : (x : T) → x ≡ t (squash x) → ⊥
f x ()

boom : ⊥
boom = f (t (squash w)) refl
