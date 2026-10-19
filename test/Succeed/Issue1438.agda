-- Andreas, 2026-09-07, issue #1438, reported by Nisse, who writes:
-- I don't think it should be possible to give fixity declarations for
-- regular names or closed operators.

postulate A : Set

infix 0 A  -- Should be rejected.

postulate ⟦_⟧ : Set

infix 0 ⟦_⟧  -- Should be rejected.

postulate B : Set → Set

syntax B A = ⟨ A ⟩

infix 0 B  -- Should be rejected.

data C : Set where
  c : C → C

pattern ⟪_⟫ x = c x

infix 0 c  -- Should be rejected.

open import Agda.Builtin.Nat renaming (zero to infix 0 zero)  -- Warning

-- Each of the infix declarations generates a
-- warning: -W[no]FixityDeclarationForNonOperator
-- Fixity declarations only apply to proper operators

--  No warning for the following:

postulate
  foo : (x y z : C) → C

infixr 42 foo
syntax foo x y z = x ⟨ z ⟩ y
