-- AIM XXIII, Andreas, 2016-04-24
-- Overloaded projections and projection patterns

-- {-# OPTIONS -v tc.proj.amb:30 #-}
-- {-# OPTIONS -v tc.lhs.split:20 #-}
{-# OPTIONS --guardedness #-}

module _ where

import Common.Level
open import Common.Prelude hiding (map)
open import Common.Equality

module M (A : Set) where
  record Stream : Set where
    coinductive
    field
      head : A
      tail : Stream
open M using (Stream)
open module S = M.Stream public

-- This is a bit trickier for overloading projections
-- as it has a parameter with is of a record type
-- with the same projections.

record _≈_ {A : Set}(s t : Stream A) : Set where
  coinductive
  field
    head : head s ≡ head t
    tail : tail s ≈ tail t
open module B = _≈_ public

≈refl : ∀{A} {s : Stream A} → s ≈ s
head ≈refl = refl
tail ≈refl = ≈refl

≈sym : ∀{A} {s t : Stream A} → s ≈ t → t ≈ s
head (≈sym p) = sym (head p)
tail (≈sym p) = ≈sym (tail p)

module N (A : Set) (s : Stream A) where
  open module SS = Stream s public

  myhead : A
  myhead = SS.head  -- cannot use ambiguous head here

map : {A B : Set} → (A → B) → Stream A → Stream B
head (map f s) = f (head s)
tail (map f s) = map f (tail s)

map_id : {A : Set}(s : Stream A) → map (λ x → x) s ≈ s
head (map_id s) = refl
tail (map_id s) = map_id (tail s)

repeat : {A : Set}(a : A) → Stream A
head (repeat a) = a
tail (repeat a) = repeat a

repeat₂ : {A : Set}(a₁ a₂ : A) → Stream A
(     (head (repeat₂ a₁ a₂))) = a₁
(head (tail (repeat₂ a₁ a₂))) = a₂
(tail (tail (repeat₂ a₁ a₂))) = repeat₂ a₁ a₂

repeat≈repeat₂ : {A : Set}(a : A) → repeat a ≈ repeat₂ a a
(     (head (repeat≈repeat₂ a))) = refl
(head (tail (repeat≈repeat₂ a))) = refl
(tail (tail (repeat≈repeat₂ a))) = repeat≈repeat₂ a
