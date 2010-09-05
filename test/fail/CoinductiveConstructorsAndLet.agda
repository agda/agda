module CoinductiveConstructorsAndLet where

open import Imports.Coinduction

data D : Set where

foo : D → ∞ D
foo x = let y = x in ♯ y

-- CoinductiveConstructorsAndLet.agda:9,24-25
-- Panic: thing out of context ([CtxId 1] is not a sub context of
-- [CtxId 3])
-- when checking that the expression y has type D
