-- Currently this test case is broken. Once Issue 3451 has been fixed
-- it should be moved to test/Fail (and this comment should be
-- removed).

-- The option --guardedness turns off sized types.

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Size

record Stream (A : Set) (i : Size) : Set where
  coinductive
  field
    head : A
    tail : {j : Size< i} → Stream A j

open Stream

postulate
  destroy-guardedness : {A : Set} → A → A

repeat : ∀ {A i} → A → Stream A i
repeat x .head = x
repeat x .tail = destroy-guardedness (repeat x)
