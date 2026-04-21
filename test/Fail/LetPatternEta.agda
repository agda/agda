-- Andreas, 2023-10-07, issue #6825, test case by Amy
-- Andreas, 2026-04-14, updated to warning

module LetPatternEta where

open import Agda.Builtin.Equality

record Wrap (A : Set) : Set where
  constructor wrap; no-eta-equality; pattern
  field unwrap : A

fails : ∀ {A : Set} (w : Wrap A) → w ≡ w
fails = λ w@(wrap a) → refl {x = wrap a}

-- fails : ∀ {A} → Wrap A → Set
-- fails w = let wrap a = w in _
