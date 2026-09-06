-- Andreas, 2026-09-06, issue #8698.
--
-- Named `where` modules are disallowed under `with` and `rewrite`
-- (error NamedWhereModuleUnderWith), but nowhere else.

{-# OPTIONS --safe --without-K #-}

module Issue8698 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

-- A named `where` module in an ordinary clause is fine.

plain : Bool
plain = local
  module P where
  local : Bool
  local = true

test-plain : Bool
test-plain = P.local

-- Anonymous `where` blocks under `with` are unaffected.

anon : Bool → Bool
anon x with x
... | true  = aux
  where
  aux : Bool
  aux = false
... | false = true

-- `using p ← e` does not with-abstract, so it does not restrict
-- named `where` modules.

usingCase : Bool → Bool
usingCase x using y ← x = q
  module U where
  q : Bool
  q = y

test-using : Bool → Bool
test-using x = U.q x
