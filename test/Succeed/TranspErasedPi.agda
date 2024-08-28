-- This test verifies that transp has the correct computational
-- behaviour on erased pi types (test case constructed by Amélia Liao)

{-# OPTIONS --erasure --erased-cubical #-}

open import Agda.Primitive renaming (Set to Type)
open import Agda.Primitive.Cubical
  renaming (primIMax to _∨_ ; primIMin to _∧_ ; primINeg to ~_ ; primTransp to transp)
open import Agda.Builtin.Cubical.Sub
  renaming (primSubOut to outS)
open import Agda.Builtin.Cubical.Path

refl : ∀ {ℓ} {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} i = x

module
  _ {ℓ ℓ′} {A0 : Type ℓ} {B0 : @0 A0 → Type ℓ′}
    (φ : I)
    {A : I → Sub (Type ℓ) φ (λ ._ → A0)}
    {B : ∀ i → (@0 x : outS (A i)) → Sub (Type ℓ′) φ (λ { (φ = i1) → B0 x })}
    (f : (@0 x : outS (A i0)) → outS (B i0 x))
  where

  _ : transp (λ i → (@0 x : outS (A i)) → outS (B i x)) φ f
    ≡ λ x → transp (λ i → outS (B i (transp (λ j → outS (A (i ∨ ~ j))) (φ ∨ i) x))) φ
    --                              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    --                                transpFill (λ i → outS (A i)) φ x but inlined
              (f (transp (λ i → outS (A (~ i))) φ x))
  _ = refl
