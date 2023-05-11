{-# OPTIONS --safe #-}

module Issue2250-2 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

cast : {A B : Set} → A ≡ B → A → B
cast refl x = x

data ⊥ : Set where
record ⊤ : Set where

-- Exploit using 'abstract'
-- Issue #2250

module Abstract where

  abstract

    f : Bool → Bool
    f x = true

    {-# INJECTIVE f #-}

    same : f true ≡ f false
    same = refl

  not-same : f true ≡ f false → ⊥
  not-same ()

  absurd : ⊥
  absurd = not-same same

-- Exploit using mutual blocks
-- AIM XXXVI (issue #6616)

module Mutual where

  F : Set → Set

  {-# INJECTIVE F #-}

  F-injective : (A B : Set) → F A ≡ F B → A ≡ B
  F-injective A B refl = refl

  F _ = Bool

  absurd : ⊥
  absurd = cast (F-injective ⊤ ⊥ refl) record{}

-- Exploit using data

module Data where

  data Lock : Set₁ where
    lock : Set → Lock

  unlock : {A B : Set} → lock A ≡ lock B → A ≡ B
  unlock refl = refl

  F : Lock → Set
  F (lock _) = Bool

  {-# INJECTIVE F #-}

  F-injective : (A B : Lock) → F A ≡ F B → A ≡ B
  F-injective A B refl = refl

  boo : ⊤ ≡ ⊥
  boo = unlock (F-injective (lock ⊤) (lock ⊥) refl)

  absurd : ⊥
  absurd = cast boo record{}
