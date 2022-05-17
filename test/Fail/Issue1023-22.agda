-- Andreas, 2014-10-05, code by Jesper Cockx

{-# OPTIONS --cubical-compatible --guardedness #-}

open import Common.Coinduction
open import Common.Equality

data False : Set where

data Pandora : Set where
  C : ∞ False → Pandora

postulate
  ext : (False → Pandora) → (Pandora → False) → False ≡ Pandora

f : False → Pandora
f ()

g : Pandora → False
g (C x) = ♭ x

foo : False ≡ Pandora
foo = ext f g

-- should be rejected
loop : (A : Set) → A ≡ Pandora → A
loop .Pandora refl = C (♯ (loop False foo))

absurd : False
absurd = loop False foo
