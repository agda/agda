module _ where

module A where

  syntax c x = ⟦ x

  data D₁ : Set where
    b : D₁
    c : D₁ → D₁

module B where

  syntax c x = ⟦ x ⟧

  data D₂ : Set where
    c : A.D₁ → D₂

open A
open B

test₁ : D₂
test₁ = ⟦ (⟦ c b) ⟧

test₂ : D₂ → D₁
test₂ ⟦ x ⟧ = ⟦ x

test₃ : D₁ → D₂
test₃ b     = c b
test₃ (⟦ x) = ⟦ x ⟧

test₄ : D₁ → D₂
test₄ A.b     = B.c A.b
test₄ (A.⟦ x) = B.⟦ x ⟧

test₅ : D₂ → D₁
test₅ B.⟦ x ⟧ = A.⟦ x

-- Should work.
