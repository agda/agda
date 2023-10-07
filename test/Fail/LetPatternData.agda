-- Andreas, 2023-10-07, issue #6825, test case by Amy

module LetPatternData where

data Wrap (A : Set) : Set where
  wrap : A → Wrap A

fails : ∀ {A} → Wrap A → Set
fails w = let wrap a = w in _
