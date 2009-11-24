{-# OPTIONS --universe-polymorphism #-}
module Issue227 where

open import Common.Level

data D (a p b : Level) (A : Set a) (P : A → Set p) : Set (p ⊔ a ⊔ b) where
  d : ((x : A) → P x) → D a p b A P

-- Unsolved trivial constraint: Set (a ⊔ p) =< Set (p ⊔ a).

OK : ∀ {a} {A : Set a} → (A → Set) → A → Set _
OK P = P

NotOK : ∀ {a} {A : Set a} → (P : A → Set) → A → Set _
NotOK P = P

-- Unsolved constraint:
-- \/ (Set (a ⊔ suc zero)) (Set (a ⊔ suc zero)) = \/ (Set (a ⊔ suc zero)) (Set (a ⊔ suc zero))