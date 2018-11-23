-- Jesper, 2018-11-23: Unsolved metas are turned into postulates
-- when --allow-unsolved-metas is enabled, but there was no internal
-- representation of postulated sorts.

module Issue3256 where

open import Issue3256.B

-- WAS:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Reduce.hs:149
