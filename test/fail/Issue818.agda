-- {-# OPTIONS -v tc.with:100 #-}
module Issue818 where

data ⊤ : Set where
  tt : ⊤

Foo : {x : ⊤} → Set₁
Foo with tt
Foo {x = _} | tt = Set

-- Panic: wrong number of arguments in with clause: given 1, expected
-- 0
-- when checking that the clause
-- Foo with tt
-- Foo {x = _} | tt = Set
-- has type {⊤} → Set₁

-- The code above type-checks using Agda 2.3.0.1, but not with Agda
-- 2.3.2.

-- Andreas, 2013-03-08: same error thrown by

-- foo : ⊤ → Set₁
-- foo with tt
-- foo x | tt = Set

-- Implicit arguments are no longer eagerly introduced (see release notes
-- for 2.3.2, text for issue 679).

-- Should now throw a proper error message (not a panic).
