-- This test case was reported by Andrea Vezzosi.

{-# OPTIONS --no-guardedness --sized-types #-}

open import Agda.Builtin.Size

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

data ⊥ : Set where

record T (i : Size) : Set where
  constructor con
  coinductive
  field
    force : Σ (Size< i) λ{ j → T j }

open T public

empty : ∀ i → T i → ⊥
empty i x with force x
... | j , y = empty j y

inh : T ∞
inh = λ{ .force → ∞ , inh } -- using ∞ < ∞ here

false : ⊥
false = empty ∞ inh
