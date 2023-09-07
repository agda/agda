module MissingDefinitions where

open import Agda.Builtin.Equality

Q : Set

data U : Set
S : Set
S = U
T : S → Set
T _ = U

V : Set
W : V → Set

private

  X : Set

module AB where

  data A : Set
  B : (a b : A) → a ≡ b

mutual

  U₂ : Set
  data T₂ : U₂ → Set
  V₂ : (u₂ : U₂) → T₂ u₂ → Set
  data W₂ (u₂ : U₂) (t₂ : T₂ u₂) : V₂ u₂ t₂ → Set

-- Andreas, 2023-09-07, issue #6823
-- Updated error to include range of names that lack a definition

-- MissingDefinitions.agda:25,1-30,50
-- The following names are declared, but not accompanied by a definition:
-- - Q (at MissingDefinitions.agda:5,1-2)
-- - U (at MissingDefinitions.agda:7,6-7)
-- - V (at MissingDefinitions.agda:13,1-2)
-- - W (at MissingDefinitions.agda:14,1-2)
-- - X (at MissingDefinitions.agda:18,3-4)
-- Since 'mutual' blocks can not participate in mutual recursion,
-- their definition must be given before this point.
