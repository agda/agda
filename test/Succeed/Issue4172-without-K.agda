{-# OPTIONS --cubical-compatible #-}

record Erased (A : Set) : Set where
  constructor [_]
  field
    @0 erased : A

open Erased

data W (A : Set) (B : A → Set) : Set where
  sup : (x : A) → (B x → W A B) → W A B

lemma :
  {A : Set} {B : A → Set} →
  Erased (W A B) → W (Erased A) (λ x → Erased (B (erased x)))
lemma [ sup x f ] = sup [ x ] λ ([ y ]) → lemma [ f y ]

data ⊥ : Set where

data E : Set where
  c : E → E

magic : @0 E → ⊥
magic (c e) = magic e
