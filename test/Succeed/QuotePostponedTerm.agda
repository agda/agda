module test.Succeed.QuotePostponedTerm where

open import Common.Reflection
open import Common.Prelude renaming (Nat to ℕ; module Nat to ℕ)

-- This macro would lead to unsolved metavariables if
-- we used 'Term' here, as Agda wrap the (λ n → n) in 'quoteTerm',
-- which then tries to infer it's type, as opposed to postponing
-- the problem until the macro unblocks it.
macro
  test : PostponedTerm → Term → TC ⊤
  test (postponed argument m) hole = do
    unify hole argument

foo : Nat → Nat
foo = test (λ n → n)
