-- Andreas, 2014-01-07 Issue reported by Dmitriy Traytel

{-# OPTIONS --guardedness --sized-types #-}

module _ where

open import Common.Size
open import Common.Prelude hiding (map)

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

-- This type should be empty.
data D : (i : Size) → Set where
  cons : ∀ i → Stream (D i) → D (↑ i)

-- BAD: But we can construct an inhabitant.
inh : Stream (D ∞)
head inh = cons ∞ inh  -- Should be rejected by termination checker.
tail inh = inh

map :  ∀{A B} → (A → B) → Stream A → Stream B
head (map f s) = f (head s)
tail (map f s) = map f (tail s)

loop : ∀ i → D i → ⊥
loop .(↑ i) (cons i s) = head (map (loop i) s)

absurd : ⊥
absurd = loop ∞ (cons ∞ inh)
