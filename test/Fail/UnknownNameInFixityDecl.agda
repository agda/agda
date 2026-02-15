-- Andreas, 2026-02-14, make UnknownNameInFixityDecl an error warning.

module UnknownNameInFixityDecl where

open import Agda.Builtin.Sigma

-- Unknown operators
infix 40 _+_                         -- _+_ should have error highlighting
infixr 60 _*_                        -- _*_ should have error highlighting

-- Cannot assign a syntax to an imported identifier.

syntax Σ A (λ x → B) = ∃ x ∈ A ∙ B   -- Σ should have error highlighting

-- This also tests #2893: warnings should be displayed even in case of hard errors:

_×_ : (A B : Set) → Set
A × B = ∃ _ ∈ A ∙ B                  -- This reports an unbound name: ∃

-- Expected errors:
--
-- error: [NotInScope]
-- Not in scope:
--   ∃
--   at ...
-- when scope checking ∃

-- error: [UnknownNamesInFixityDecl]
-- The following names are not declared in the same scope as their
-- syntax or fixity declaration (i.e., either not in scope at all,
-- imported from another module, or declared in a super module): _*_, _+_, Σ
