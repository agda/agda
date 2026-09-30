-- Andreas, 2017-04-24, issue #2552
-- Let bindings in top-level module telescope
-- make top-level interactive commands crash.

-- {-# OPTIONS -v interaction.top:20 #-}

open import Agda.Primitive

module _ (let foo = lzero) (A : Set) where

-- C-c C-n A

-- WAS:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/Interaction/BasicOps.hs:882

-- Should work now

-- Still problematic:

-- C-c C-n foo
-- Panic: unbound variable foo
-- when inferring the type of foo
