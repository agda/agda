-- Andreas, 2026-02-07, issue #8374

-- This fixity declaration should NOT apply to the operator in the following module.
infixr 20 _∷_

-- Expected warning: -W[no]UnknownNamesInFixityDecl
-- The following names are not declared in the same scope as their
-- syntax or fixity declaration (i.e., either not in scope at all,
-- imported from another module, or declared in a super module): _∷_

module M (A : Set) where
  data List : Set where
    [] : List
    _∷_ : A → List → List

open M

-- This needs the fixity to parse, so we expect a parse error.

dup : {A : Set} (a : A) → List A
dup a = a ∷ a ∷ []

-- Expected error: [NoParseForApplication]
-- Could not parse the application a ∷ a ∷ []
-- Operators used in the grammar:
--   ∷ (infix operator, level 20) [_∷_ (...)]
-- when scope checking a ∷ a ∷ []
