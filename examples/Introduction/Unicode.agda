
-- Agda supports full unicode everywhere. An Agda file should be written using
-- the UTF-8 encoding.

module Introduction.Unicode where

module ユーニコード where

  data _∧_ (P Q : Prop) : Prop where
    ∧-intro : P -> Q -> P ∧ Q

  ∧-elim₁ : {P Q : Prop} -> P ∧ Q -> P
  ∧-elim₁ (∧-intro p _) = p

  ∧-elim₂ : {P Q : Prop} -> P ∧ Q -> Q
  ∧-elim₂ (∧-intro _ q) = q

  data _∨_ (P Q : Prop) : Prop where
    ∨-intro₁ : P -> P ∨ Q
    ∨-intro₂ : Q -> P ∨ Q

  ∨-elim : {P Q R : Prop} -> (P -> R) -> (Q -> R) -> P ∨ Q -> R
  ∨-elim f g (∨-intro₁ p) = f p
  ∨-elim f g (∨-intro₂ q) = g q

  data ⊥ : Prop where

  data ⊤ : Prop where
    ⊤-intro : ⊤

  data ¬_ (P : Prop) : Prop where
    ¬-intro : (P -> ⊥) -> ¬ P

  data ∏ {A : Set}(P : A -> Prop) : Prop where
    ∏-intro : ((x : A) -> P x) -> ∏ P

