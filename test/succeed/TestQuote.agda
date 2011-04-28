module TestQuote where

{- test of reflection, implementing a trivial prover. -}

open import Common.Reflect
open import Common.Prelude
open import Common.Level

_==_ : Term → Term → Bool
def x [] == def y [] = primQNameEquality x y
_        == _        = false

data ⊥ : Set where
record ⊤ : Set where

data Thm : Set where
  triv : Thm

`Thm = def (quote Thm) []

⟦_⟧ : Term → Set
⟦ goal ⟧ with goal == `Thm
...     | true  = Thm
...     | false = ⊥

Hyp : Term → Set → Set
Hyp goal A with goal == `Thm
...        | true  = ⊤
...        | false = A

solve : (goal : Term) → Hyp goal ⟦ goal ⟧ → ⟦ goal ⟧ 
solve goal h  with goal == `Thm
...      | true = triv
...      | false = h

test₁ : Thm
test₁ = quoteGoal t in solve t _
