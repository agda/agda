-- 2014-05-16 Andreas: Question mark not recognized by emacs

module _ where

data Nat : Set where
  suc : Nat → Nat

data Fin : Nat → Set where
  zero : ∀ n → Fin (suc n)

test : ∀ n → Fin n → Set
test .? (zero n) = Nat

-- The questionmark in the dot pattern is not recognized by emacs-mode.

-- This cannot be tested by test/interaction, but I still put the test case here.
