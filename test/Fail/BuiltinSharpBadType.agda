
data ⊥ : Set where

postulate
  ∞  : ∀ {a} → Set a → Set a
  ♯_ : ∀ {a} {A : Set a} → (A → ⊥) → ∞ A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
