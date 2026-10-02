open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat

module RecordWhereInCtx (A : Set) where

it : Σ Nat λ _ → Nat
it = record where
  fst = 1
  snd = 2
