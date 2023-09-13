-- Andreas, 2023-10-07, issue #6825, test case by Amy

module LetPatternEta where

record Wrap (A : Set) : Set where
  constructor wrap; no-eta-equality; pattern
  field unwrap : A

fails : ∀ {A} → Wrap A → Set
fails = \(wrap a) → a

-- fails : ∀ {A} → Wrap A → Set
-- fails w = let wrap a = w in _
