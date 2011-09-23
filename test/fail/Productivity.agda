module Productivity (char : Set) where

  open import Imports.Coinduction

  infix  50 _⋆ _+
  infixl 40 _⊛_
  infixl 30 _∣_

  data P : Set where
    ε   : P
    sym : char -> P
    _⊛_ : ∞ P -> ∞ P -> P
    _∣_ : ∞ P -> ∞ P -> P

  mutual

    _⋆ : P -> P
    p ⋆ = ♯ ε ∣ ♯ (p +)

    _+ : P -> P
    p + = ♯ p ⊛ ♯ (p ⋆)

  _sepBy_ : P -> P -> P
  p sepBy sep = ♯ p ⊛ ♯ ((♯ sep ⊛ ♯ p) ⋆)

  postulate
    addOp  : P
    mulOp  : P
    number : P
    openP  : char
    closeP : char

  -- Not guarded:

  mutual
    expr   = term sepBy addOp
    term   = factor sepBy mulOp
    factor = ♯ number ∣ ♯ (♯ (♯ sym openP ⊛ ♯ expr) ⊛ ♯ sym closeP)

  -- Guarded and incomprehensible:

  mutual
    expr₁ = ♯ term₁ ⊛ ♯ expr₂
    expr₂ = ♯ ε ∣ ♯ expr₃
    expr₃ = ♯ (♯ addOp ⊛ ♯ term₁) ⊛ ♯ expr₂

    term₁ = ♯ factor₁ ⊛ ♯ term₂
    term₂ = ♯ ε ∣ ♯ term₃
    term₃ = ♯ (♯ mulOp ⊛ ♯ factor₁) ⊛ ♯ term₂

    factor₁ = ♯ number ∣ ♯ (♯ (♯ sym openP ⊛ ♯ expr₁) ⊛ ♯ sym closeP)
