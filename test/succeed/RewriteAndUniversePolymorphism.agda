
module RewriteAndUniversePolymorphism where

open import Common.Equality

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

test : (a b : ℕ) → a ≡ b → b ≡ a
test a b eq rewrite eq = refl
