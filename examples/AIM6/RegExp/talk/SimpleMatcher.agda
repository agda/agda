------------------------------------------------------------------------
-- Simple regular expression matcher
------------------------------------------------------------------------

open import Eq
open import Setoids
open import Prelude
import RegExps

module SimpleMatcher (D : Datoid) where

private
  open module D' = Datoid D
  open module S' = Setoid setoid
  open module R  = RegExps setoid

infix 4 _∈‿⟦_⟧¿

------------------------------------------------------------------------
-- A lemma

private

  lemma : forall {a x xs₂}
    -> (xs₁ : [ a ]) -> (xs₁ ++ x ∷ []) ++ xs₂ ≡ xs₁ ++ x ∷ xs₂
  lemma []       = refl
  lemma (x ∷ xs) = cong (\ys -> x ∷ ys) (lemma xs)

------------------------------------------------------------------------
-- Regular expression matcher

-- The type of _∈‿⟦_⟧¿ documents its soundness (assuming that the code
-- is terminating). To prove completeness more work is necessary.

matches-⊙¿ : forall xs₁ xs₂ re₁ re₂
             -> Maybe (xs₁ ++ xs₂ ∈‿⟦ re₁ ⊙ re₂ ⟧)

_∈‿⟦_⟧¿ : (xs : [ carrier ]) -> (re : RegExp) -> Maybe (xs ∈‿⟦ re ⟧)
[]     ∈‿⟦ ε ⟧¿         = just matches-ε
_ ∷ [] ∈‿⟦ • ⟧¿         = just matches-•
x ∷ [] ∈‿⟦ sym y ⟧¿     with x ≟ y
x ∷ [] ∈‿⟦ sym y ⟧¿     | yes eq = just (matches-sym eq) 
x ∷ [] ∈‿⟦ sym y ⟧¿     | no _   = nothing
xs     ∈‿⟦ re₁ ∣ re₂ ⟧¿ with xs ∈‿⟦ re₁ ⟧¿
xs     ∈‿⟦ re₁ ∣ re₂ ⟧¿ | just m  = just (matches-∣ˡ m)
xs     ∈‿⟦ re₁ ∣ re₂ ⟧¿ | nothing with xs ∈‿⟦ re₂ ⟧¿
xs     ∈‿⟦ re₁ ∣ re₂ ⟧¿ | nothing | just m  = just (matches-∣ʳ m)
xs     ∈‿⟦ re₁ ∣ re₂ ⟧¿ | nothing | nothing = nothing
xs     ∈‿⟦ re₁ ⊙ re₂ ⟧¿ = matches-⊙¿ [] xs re₁ re₂
[]     ∈‿⟦ re ⋆ ⟧¿      = just (matches-⋆ (matches-∣ˡ matches-ε))
x ∷ xs ∈‿⟦ re ⋆ ⟧¿      with matches-⊙¿ (x ∷ []) xs re (re ⋆)
x ∷ xs ∈‿⟦ re ⋆ ⟧¿      | just m  = just (matches-⋆ (matches-∣ʳ m))
x ∷ xs ∈‿⟦ re ⋆ ⟧¿      | nothing = nothing
_      ∈‿⟦ _ ⟧¿         = nothing

matches-⊙¿ xs₁ xs₂ re₁ re₂ with xs₁ ∈‿⟦ re₁ ⟧¿ | xs₂ ∈‿⟦ re₂ ⟧¿
matches-⊙¿ xs₁ xs₂ re₁ re₂ | just m₁ | just m₂ = just (matches-⊙ m₁ m₂)
matches-⊙¿ xs₁ [] re₁ re₂ | _ | _ = nothing
matches-⊙¿ xs₁ (x ∷ xs₂) re₁ re₂ | _ | _ =
  subst (\xs -> Maybe (xs ∈‿⟦ re₁ ⊙ re₂ ⟧))
        (lemma xs₁)
        (matches-⊙¿ (xs₁ ++ x ∷ []) xs₂ re₁ re₂)
