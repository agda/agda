-- Jesper, 2018-10-16: When solving constraints produces a term which
-- contains the same unsolved metavariable twice, only the first
-- occurrence should be turned into an interaction hole.

open import Agda.Builtin.Equality

postulate Id : (A : Set) → A → A → Set

allq : (∀ m n → Id _ m n) ≡ {!!}
allq = refl
