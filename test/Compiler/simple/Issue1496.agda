module Issue1496 where

open import Common.Unit
open import Common.String
open import Common.Char
open import Common.List
open import Common.IO

-- Agda infers that the "a" level argument to return has to be
-- Agda.Primitive.lzero.
main : IO Unit
main = return unit
