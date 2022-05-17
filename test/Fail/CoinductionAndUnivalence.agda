{- Jesper Cockx, 26-05-2014
   Issue 1023
   Example by Maxime Denes, adapted by Andreas Abel
-}

{-# OPTIONS --cubical-compatible --guardedness #-}

module CoinductionAndUnivalence where

open import Common.Coinduction
open import Common.Equality

prop = Set

data False : prop where

magic : ∀ {a} {A : Set a} → False → A
magic ()

data Pandora : prop where
  C : ∞ False → Pandora

postulate
  ext : (f : False → Pandora) → (g : Pandora → False) →
        (∀ x → f (g x) ≡ x) → (∀ y → g (f y) ≡ y) →
        False ≡ Pandora

foo : False ≡ Pandora
foo = ext f g fg gf
  where
    f : False → Pandora
    f ()

    g : Pandora → False
    g (C c) = ♭ c

    fg : ∀ x → f (g x) ≡ x
    fg x = magic (g x)

    gf : ∀ y → g (f y) ≡ y
    gf ()

loop : False
loop rewrite foo = C (♯ loop)
