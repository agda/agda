-- Andreas, 2020-02-18, issue #4450 raised by Nisse
--
-- ETA pragma should be considered unsafe, since type-checking may loop.

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Equality

record R : Set where
 coinductive
 field
   force : R
open R

{-# ETA R #-}

foo : R
foo .force .force = foo

test : foo .force ≡ foo
test = refl

-- WAS:
-- test makes type checker loop;
-- ETA with --safe is a soft error and only raised after
-- the whole file is processed.

-- NOW, 2023-08-30:
-- ETA with --safe is a hard error
-- See https://github.com/agda/agda/pull/6798#issuecomment-1697305150
