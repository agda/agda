open import Agda.Builtin.List
open import Agda.Builtin.Char

foo : Char → List Char
foo c = c ∷ []

-- Step 1: case split on foo-ls
case-split-test₁ : List Char → List Char
case-split-test₁ ('-' ∷ ls) with (foo '+')
... | foo-ls = {!foo-ls!}
case-split-test₁ ls = ls

-- Step 2: expand ellipsis
case-split-test₂ : List Char → List Char
case-split-test₂ ('-' ∷ ls) with (foo '+')
... | [] = {!.!}
... | x ∷ foo-ls = {!.!}
case-split-test₂ ls = ls

-- WAS: case splitting on foo-ls produces:
--   case-split-test (.'-' ∷ ls) | [] = ?
--   case-split-test (.'-' ∷ ls) | x ∷ foo-ls = ?
-- SHOULD: not put dots in front of literal patterns:
--   case-split-test ('-' ∷ ls) | [] = {!!}
--   case-split-test ('-' ∷ ls) | x ∷ foo-ls = {!!}
