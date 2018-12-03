open import Agda.Builtin.List
open import Agda.Builtin.Char

foo : Char → List Char
foo c = c ∷ []

case-split-test : List Char → List Char
case-split-test ('-' ∷ ls) with (foo '+')
... | foo-ls = {!foo-ls!}
case-split-test ls = ls

-- WAS: case splitting on foo-ls produces:
--   case-split-test (.'-' ∷ ls) | [] = ?
--   case-split-test (.'-' ∷ ls) | x ∷ foo-ls = ?
-- SHOULD: not put dots in front of literal patterns:
--   case-split-test ('-' ∷ ls) | [] = {!!}
--   case-split-test ('-' ∷ ls) | x ∷ foo-ls = {!!}
