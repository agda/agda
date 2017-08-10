-- Andreas, 2017-08-10, issue #2667, reported by xekoukou,
-- test case by gallais

-- {-# OPTIONS -v tc.with.split:40 #-}

data Bot : Set where

data A : Set where
  s  : A → A

data P : A → Set where
  p : ∀ {a} → P (s a)

poo : ∀{b} → P b → Set
poo p with Bot
poo {b = s c} p | _ = P c

-- Error WAS (2.5.3): Panic, unbound variable c

-- Expected (as in 2.5.2):
--
-- Inaccessible (dotted) patterns from the parent clause must also be
-- inaccessible in the with clause, when checking the pattern {b = s c},
-- when checking that the clause
-- poo p with Bot
-- poo {b = s c} p | _ = P c
-- has type {b : A} → P b → Set

-- Ideally: succeed.
