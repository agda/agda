open import Agda.Builtin.Float
open import Agda.Builtin.Nat
open import Agda.Builtin.Int
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma

open import Common.Unit
open import Common.IO
open import Agda.Builtin.String

-- Using this function (instead of `with` clauses) avoids
-- compile-time evaluation, which can hide backend bugs
case_of_ : {A B : Set} → A → (A → B) → B
case x of f = f x

r = case primFloatRound 1234.5 of λ where
  (just (pos n)) → n + n + 4
  _ → 0

f = case primFloatFloor 1234.5 of λ where
  (just (pos n)) → n + n + 4
  _ → 0

c = case primFloatCeiling 1234.5 of λ where
  (just (pos n)) → n + n + 4
  _ → 0

tr = case primFloatToRatio 1234.5 of λ where
  (pos m , pos n) → m + n + 4
  _ → 0

d = case primFloatDecode 1234.5 of λ where
  (just (pos m , pos n)) → m + n + 4
  _ → 0

main : IO Unit
main = putStr "OK"
