-- Andreas, 2026-10-29, issue #8881, reported and test case by typeterrorist.
-- Level constraints  _j ≤ i ⊔ j  and  _j = i ⊔ j ⊔ _j  should be solved.

open import Agda.Primitive

postulate
  R : ∀ {i j} → Set i → Set j → Set (i ⊔ j)
  e : ∀ {i} {A : Set i} → R A A
  F : ∀ {k} {B : Set k} → (B → R B B) → R B B

record Op {p q} (P : Set p) (Q : Set q) : Set (p ⊔ q) where
  field _∙_ : P → Q → Q

open Op ⦃ ... ⦄

postulate instance
  op : ∀ {i j} {A : Set i} {C : Set j} → Op (R A A) (R A C)

test : ∀ {i j} {X : Set (i ⊔ j)} → R X X → R X X
test r = F (λ _ → r ∙ e) ∙ r

-- Should succeed.
