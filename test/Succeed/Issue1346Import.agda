-- Andreas, 2019-08-17, issue #1346

open import Issue1346

-- Repeating the definitions of Issue1346.agda

private
  test₁ : List⁺ Bool
  test₁ = true ∷ false ∷ []  -- mixing _∷_ of _×_ and List

  test₂ : ∀{A : Set} → A → List A × List⁺ A × List⁺ A
  test₂ a = [] , a ∷ [] , a ∷ a ∷ []  -- mixing _,_ and _∷_ of _×_
