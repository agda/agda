------------------------------------------------------------------------
-- Regular expressions
------------------------------------------------------------------------

open import Setoids

module RegExps (S : Setoid) where

infix  8 _⋆
infixl 7 _⊙_
infixl 6 _∣_
infix  1 _∈‿⟦_⟧

open import Prelude
private open module S' = Setoid S

------------------------------------------------------------------------
-- Regular expressions

data RegExp : Set where
  ∅   : RegExp                      -- Matches nothing.
  ε   : RegExp                      -- Matches the empty string.
  •   : RegExp                      -- Matches any single character.
  sym : carrier -> RegExp           -- Matches the given character.
  _⋆  : RegExp -> RegExp            -- Kleene star.
  _∣_ : RegExp -> RegExp -> RegExp  -- Choice.
  _⊙_ : RegExp -> RegExp -> RegExp  -- Sequencing.

------------------------------------------------------------------------
-- Size of a regular expression

size : RegExp -> ℕ
size (re ⋆)      = 1 + size re
size (re₁ ∣ re₂) = 1 + size re₁ + size re₂
size (re₁ ⊙ re₂) = 1 + size re₁ + size re₂
size _           = 1

------------------------------------------------------------------------
-- Semantics of regular expressions

-- The type xs ∈‿⟦ re ⟧ is inhabited iff xs matches the regular
-- expression re.

data _∈‿⟦_⟧ : [ carrier ] -> RegExp -> Set where
  matches-ε   : [] ∈‿⟦ ε ⟧
  matches-•   : forall {x} -> x ∷ [] ∈‿⟦ • ⟧
  matches-sym : forall {x y} -> x ≈ y -> x ∷ [] ∈‿⟦ sym y ⟧
  matches-⋆   : forall {xs re}
              -> xs ∈‿⟦ ε ∣ re ⊙ re ⋆ ⟧ -> xs ∈‿⟦ re ⋆ ⟧
  matches-∣ˡ   : forall {xs re₁ re₂}
              -> xs ∈‿⟦ re₁ ⟧ -> xs ∈‿⟦ re₁ ∣ re₂ ⟧
  matches-∣ʳ   : forall {xs re₁ re₂}
              -> xs ∈‿⟦ re₂ ⟧ -> xs ∈‿⟦ re₁ ∣ re₂ ⟧
  matches-⊙   : forall {xs₁ xs₂ re₁ re₂}
              -> xs₁ ∈‿⟦ re₁ ⟧ -> xs₂ ∈‿⟦ re₂ ⟧
              -> xs₁ ++ xs₂ ∈‿⟦ re₁ ⊙ re₂ ⟧

------------------------------------------------------------------------
-- Is the regular expression bypassable?

bypassable : (re : RegExp) -> Maybe ([] ∈‿⟦ re ⟧)
bypassable ∅           = nothing
bypassable ε           = just matches-ε
bypassable •           = nothing
bypassable (sym _)     = nothing
bypassable (re ⋆)      = just (matches-⋆ (matches-∣ˡ matches-ε))
bypassable (re₁ ∣ re₂) with bypassable re₁ | bypassable re₂
bypassable (re₁ ∣ re₂) | just m  | _       = just (matches-∣ˡ m)
bypassable (re₁ ∣ re₂) | nothing | just m  = just (matches-∣ʳ m)
bypassable (re₁ ∣ re₂) | nothing | nothing = nothing
bypassable (re₁ ⊙ re₂) with bypassable re₁ | bypassable re₂
bypassable (re₁ ⊙ re₂) | just m₁ | just m₂ = just (matches-⊙ m₁ m₂)
bypassable (re₁ ⊙ re₂) | _       | _       = nothing
