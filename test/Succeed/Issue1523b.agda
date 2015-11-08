-- {-# OPTIONS --copatterns #-}
-- {-# OPTIONS -v tc.lhs:20 #-}

open import Common.Size

record Stream (i : Size) (A : Set) : Set where
  coinductive
  constructor _::_
  field
    head  : A
    tail  : ∀ {j : Size< i} → Stream j A
open Stream public

-- size forgetful cons
cons : ∀ i {A} → A → Stream i A → Stream (↑ i) A
cons i a as = a :: as

-- Should work
