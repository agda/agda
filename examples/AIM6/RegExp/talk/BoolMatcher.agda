------------------------------------------------------------------------
-- Simple regular expression matcher (without soundness proof)
------------------------------------------------------------------------

open import Eq
open import Setoids
open import Prelude
import RegExps

module BoolMatcher (D : Datoid) where

private
  open module D' = Datoid D
  open module S' = Setoid setoid
  open module R  = RegExps setoid

infix 4 _∈‿⟦_⟧¿

------------------------------------------------------------------------
-- Helper function

decToBool : forall {x y} -> Dec (x ≈ y) -> Bool
decToBool (yes _) = true
decToBool (no _)  = false

------------------------------------------------------------------------
-- Regular expression matcher

matches-⊙¿ : (xs₁ xs₂ : [ carrier ]) -> (re₁ re₂ : RegExp) -> Bool

_∈‿⟦_⟧¿ : (xs : [ carrier ]) -> (re : RegExp) -> Bool
[]     ∈‿⟦ ε ⟧¿         = true
x ∷ [] ∈‿⟦ • ⟧¿         = true
x ∷ [] ∈‿⟦ sym y ⟧¿     = decToBool (x ≟ y)
xs     ∈‿⟦ re₁ ∣ re₂ ⟧¿ = xs ∈‿⟦ re₁ ⟧¿ ∨ xs ∈‿⟦ re₂ ⟧¿
xs     ∈‿⟦ re₁ ⊙ re₂ ⟧¿ = matches-⊙¿ [] xs re₁ re₂
[]     ∈‿⟦ re ⋆ ⟧¿      = true
x ∷ xs ∈‿⟦ re ⋆ ⟧¿      = matches-⊙¿ (x ∷ []) xs re (re ⋆)
_      ∈‿⟦ _ ⟧¿         = false


matches-⊙¿ xs₁ xs₂       re₁ re₂ with xs₁ ∈‿⟦ re₁ ⟧¿ ∨ xs₂ ∈‿⟦ re₂ ⟧¿
matches-⊙¿ xs₁ xs₂       re₁ re₂ | true  = true
matches-⊙¿ xs₁ []        re₁ re₂ | false = false
matches-⊙¿ xs₁ (x ∷ xs₂) re₁ re₂ | false =
  matches-⊙¿ (xs₁ ++ x ∷ []) xs₂ re₁ re₂
