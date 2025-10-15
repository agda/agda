module Issue8112a where

postulate A B : Set

record R : Set₁ where field f1 : Set
open R

record S (A : Set) : Set₂ where field T : Set₁
open S

postulate fun : (X : Set) ⦃ t : S X ⦄ → t .T → X

instance
  S-A : ∀ {X} ⦃ _ : S X ⦄ → S (A → X)
  S-A ⦃ i ⦄ = record { T = A → i .T }

  S-B : S B
  S-B = record { T = R }

_ : A → B
-- sanity check that illegal dot patterns don't get postponed, #8112:
_ = fun (A → B) λ where
  a .fun → A

