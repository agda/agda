module _ where

module A where

  data D₁ : Set where
    a : D₁
    c : D₁ → D₁

module B where

  data D₂ : Set where
    b : D₂
    c : D₂ → D₂

  syntax c x = ⟦ x ⟧

open A
open B

test : D₁
test = ⟦ a ⟧  -- The syntax declaration applies to B.c, not A.c.
