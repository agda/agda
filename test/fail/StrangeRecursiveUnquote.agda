open import Common.Prelude renaming (Nat to ℕ)
open import Common.Reflect

module StrangeRecursiveUnquote where

`ℕ : Term
`ℕ = def (quote ℕ) []

-- the term f n is stuck and so we cannot unquote (as expected)
f : ℕ → Term
f zero    = `ℕ
f (suc n) = unquote (f n)
