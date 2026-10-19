module Issue8112 where

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
-- checking the extended lambda is blocked on the instance meta being
-- solved, but this was not one of the deferrable errors, see #8112
_ = fun (A → B) λ where
  a .f1 → A

