-- Andreas, 2025-11-12, issue #2561
-- Meta-variable in record declaration was messed up.
-- Issue was fixed in 2.6.2.1.

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_

postulate A : Set

mutual
  record R : Set where

    foo : A → A
    foo = λ x → {!!}  -- This should be solved to ?0 := x

    field bar : A  -- WAS: with this field, the meta in foo is not longer solved

    inst : ∀ (p : A × A) → foo (proj₁ p) ≡ proj₁ p
    inst p = refl

    field boo : A

-- C-c C-s should succeed here
