-- Andreas, 2023-10-07, issue #6825, test case by Amy

module TelescopePatternEta where

record Wrap (A : Set) : Set where
  constructor wrap; no-eta-equality; pattern
  field unwrap : A

module _ {A} (w@(wrap a) : Wrap A) where
