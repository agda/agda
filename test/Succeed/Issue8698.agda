-- Andreas, 2026-09-06, issue #8698.
--
-- Named `where` modules are now disallowed under `with` and `rewrite`
-- but still allowed under `using`.

{-# OPTIONS --safe #-}

module Issue8698 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

-- `using p ← e` does not with-abstract, so it does not restrict
-- named `where` modules.

usingCase : Bool → Bool
usingCase x using y ← x = q
  module U where
  q : Bool
  q = y

test-using : Bool → Bool
test-using x = U.q x

-- Anonoymously named where modules should still be allowed.

foo : Bool
foo with Set
foo | _ = b
  module _ where
    b : Bool
    b = true
