module test.Succeed.QuotePostponedTerm where

open import Common.Reflection
open import Common.Prelude renaming (Nat to ℕ; module Nat to ℕ)

-- This macro would lead to unsolved metavariables if
-- we used 'Term' here, as Agda wrap the (λ n → n) in 'quoteTerm',
-- which then tries to infer it's type, as opposed to postponing
-- the problem until the macro unblocks it.
macro
  test : PostponedTerm → Term → TC ⊤
  test chk hole = do
    tp ← inferType hole
    tm ← elaborate chk tp
    unify hole tm

foo : Nat → Nat
foo = test (λ n → n)
