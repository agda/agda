{-# OPTIONS --guardedness #-}
-- {-# OPTIONS -v tc.lhs.split:50 -v tc.cover:20 -v tc.cc:15 -v tc.lhs.top:10 #-}
-- {-# OPTIONS -v term:20 #-}
-- {-# OPTIONS --no-positivity-check #-}
-- {-# OPTIONS -v tc.def.fun:50  #-}
-- {-# OPTIONS -v 100  #-}
module CoPatStream where

import Common.Level
open import Common.Prelude hiding (map)
open import Common.Equality

record Stream (A : Set) : Set where
  coinductive
  constructor cons
  field
    head : A
    tail : Stream A
module S = Stream

record _≈_ {A : Set}(s t : Stream A) : Set where
  coinductive
  field
    head : S.head s ≡ S.head t
    tail : S.tail s ≈ S.tail t
module B = _≈_

repeat : {A : Set}(a : A) → Stream A
-- repeat a = cons a (repeat a)
S.head (repeat a) = a
S.tail (repeat a) = repeat a

module Cycle where

  cycle : Nat -> Stream Nat
  cycle n = cycle' n where
    cycle' : Nat -> Stream Nat
    S.head (cycle' n) = n
    S.tail (cycle' zero    ) = cycle n
    S.tail (cycle' (suc n')) = cycle' n'

module CoPat where

  map : {A B : Set} → (A → B) → Stream A → Stream B
  S.head (map f s) = f (S.head s)
  S.tail (map f s) = map f (S.tail s)

  map_id : {A : Set}(s : Stream A) → map (λ x → x) s ≈ s
  B.head (map_id s) = refl
  B.tail (map_id s) = map_id (S.tail s)

module HandTranslated where

  {-# NON_TERMINATING #-}
  map : {A B : Set} → (A → B) → Stream A → Stream B
  map f s = record
    { head = f (S.head s)
    ; tail = map f (S.tail s)
    }

  {- rejected because map is not unfolded
  {-# NON_TERMINATING #-}
  map_id : {A : Set}(s : Stream A) → map (λ x → x) s ≈ s
  map_id s = record
    { head = refl
    ; tail = map_id (S.tail s)
    }
  -}

module DeepCoPat where

  repeat₂ : {A : Set}(a₁ a₂ : A) → Stream A
  (       (S.head (repeat₂ a₁ a₂))) = a₁
  (S.head (S.tail (repeat₂ a₁ a₂))) = a₂
  (S.tail (S.tail (repeat₂ a₁ a₂))) = repeat₂ a₁ a₂

  repeat≈repeat₂ : {A : Set}(a : A) → repeat a ≈ repeat₂ a a
  (       (B.head (repeat≈repeat₂ a))) = refl
  (B.head (B.tail (repeat≈repeat₂ a))) = refl
  (B.tail (B.tail (repeat≈repeat₂ a))) = repeat≈repeat₂ a

module ProjectionRHS where

  repeat′ : {A : Set}(a : A) → Stream A
  (       (S.head (repeat′ a))) = a
  (S.head (S.tail (repeat′ a))) = a
  (S.tail (S.tail (repeat′ a))) = S.tail (repeat′ a)

-- -- Type error:
--   repeat≈repeat′ : {A : Set}(a : A) → repeat a ≈ repeat′ a
--   (       (B.head (repeat≈repeat′ a))) = refl
--   (B.head (B.tail (repeat≈repeat′ a))) = refl
--   (B.tail (B.tail (repeat≈repeat′ a))) = repeat≈repeat′ a
