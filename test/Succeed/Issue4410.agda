{-# OPTIONS --rewriting --prop #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  P : Prop
  p : P
  f : P -> P

  g : {A : Set} -> P -> A -> A
  eq : ∀{A} {x : A} -> g p x ≡ x

{-# REWRITE eq #-}

module _ {A : Set} {x : A} {y : P} where

  foo : g p x ≡ x
  foo = refl

  bar : g (f y) x ≡ x
  bar = refl
