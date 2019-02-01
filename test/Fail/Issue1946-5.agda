-- This test case was reported by Andrea Vezzosi.
{-# OPTIONS --no-guardedness #-}
open import Agda.Builtin.Size

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

data ⊥ : Set where

record T (i : Size) : Set where
  constructor con
  coinductive
  field
    force : Σ (Size< i) \ { j → T j }

open T public

empty : ∀ i → T i → ⊥
empty i x with force x
... | j , y = empty j y

inh : T ∞
inh = \ { .force → ∞ , inh } -- using oo < oo here

false : ⊥
false = empty ∞ inh
