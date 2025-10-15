-- Andreas, 2025-08-06, issue #8048
-- Reported and test case by Satoshi Takimoto.
-- Hidden @tick arguments were not checked, so one could have unsound
-- guarding using instance @tick arguments.

{-# OPTIONS --cubical --guarded #-}

-- {-# OPTIONS -v tc.term.lock:50 #-}

module Issue8048 where

open import Agda.Primitive

primitive
  primLockUniv : Set₁

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : primLockUniv
  A    : Set

▹_ : Set → Set
▹_ A = {{@tick α : Tick}} → A

-- All of the following should fail, but we only activate the first
-- so that the test is more robust.

join : ▹ ▹ A → ▹ A
join x = x

-- Should raise error: [ReferencesFutureVariables]
-- The lock variable α can not appear simultaneously in the "later"
-- term x and in the lock term ⦃ α ⦄
-- when checking that the expression x has type A

-- -- WAS: Still typechecks
-- join1 : ▹ ▹ A → ▹ A
-- join1 x {{α}} = x {{α}}

-- -- This raises the ReferenceFutureVariables error
-- join2 : ▹ ▹ A → ▹ A
-- join2 x {{α}} = x {{α}} {{α}}
