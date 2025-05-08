-- Andreas, 2025-05-07, issue #7862, report and test case by Jonathan Chan
-- Matching against non-eta record constructors should count as proper match
-- just like for data constructors.

-- {-# OPTIONS -v tc.polarity:15 #-}
-- {-# OPTIONS -v tc.pos:40 #-}

open import Agda.Builtin.Equality

module _ (A : Set) (_<_ : A → A → Set) where

record Acc (k : A) : Set where
  pattern
  inductive
  no-eta-equality -- this makes it behave like a data constructor
  constructor acc<
  field acc : ∀ j → j < k → Acc j

-- Behavior should be the same as for data type:
--
-- data Acc (k : A) : Set where
--   acc< : (∀ j → j < k → Acc j) → Acc k

module _ (U' : ∀ k → (U< : ∀ j → j < k → Set) → Set) where

  U< : ∀ {k} → Acc k → ∀ j → j < k → Set
  U< (acc< f) j j<k = U' j (U< (f j j<k))

  lemma : ∀ {i j} (accj₁ accj₂ : Acc j) (i<j₁ i<j₂ : i < j) → U< accj₁ i i<j₁ ≡ U< accj₂ i i<j₂
  lemma accj₁ accj₂ i<j₁ i<j₂ = refl

-- WAS: refl was accepted because U< was deemed constant in its Acc argument
--
-- Expected error: [UnequalTerms]
-- accj₁ != accj₂ of type Acc j
-- when checking that the expression refl has type
-- U< accj₁ i i<j₁ ≡ U< accj₂ i i<j₂
