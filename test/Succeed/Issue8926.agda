-- Andreas, 2026-11-18, issue #8926
-- Renaming identifiers with attached syntax to operators.

module Issue8926 where

open import Agda.Builtin.Equality

module M where
  data Tree : Set where
    leaf : Tree
    suc : Tree → Tree
    pair _◇_ : Tree → Tree → Tree

  syntax suc x = x +1

  infixr 35 pair
  syntax pair x y = x plus y

  infixr 30 _◇_

module Explicit where
  open M using (leaf; _◇_) renaming (suc to infixl 42 _↑; pair to infixl 40 _⊕_)
  open M using (pair)

  postfix : leaf ↑ ↑ ≡ _↑ (_↑ leaf)
  postfix = refl

  associativity : ∀ a b c → a ⊕ b ⊕ c ≡ (a ⊕ b) ⊕ c
  associativity a b c = refl

  precedence : ∀ a b c → a ⊕ b ◇ c ≡ (a ⊕ b) ◇ c
  precedence a b c = refl

  original : ∀ a b → (a plus b) ≡ (a ⊕ b)
  original a b = refl

module Default where
  open M using () renaming (pair to _⊕_; _◇_ to _◆_)

  precedence : ∀ a b c → a ⊕ b ◆ c ≡ a ⊕ (b ◆ c)
  precedence a b c = refl

  inherited : ∀ a b c → a ◆ b ◆ c ≡ a ◆ (b ◆ c)
  inherited a b c = refl

module Closed = M using () renaming (pair to begin_via_end)

closed : ∀ a b → Closed.begin a via b end ≡ M.pair a b
closed a b = refl

-- Problem was: the operators coming from a renaming did not parse,
-- as they inherited the attached syntax.

-- Should succeed.
