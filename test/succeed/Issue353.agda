-- {-# OPTIONS -v tc.polarity:10 #-}
module Issue353 where

data Func : Set₁ where
  K : (A : Set) → Func

-- Doesn't work.
module M where

  const : ∀ {A B : Set₁} → A → B → A
  const x = λ _ → x

  ⟦_⟧ : Func → Set → Set
  ⟦ K A ⟧ X = const A X

  data μ (F : Func) : Set where
    ⟨_⟩ : ⟦ F ⟧ (μ F) → μ F

  -- Error: μ is not strictly positive, because it occurs in the second
  -- argument to ⟦_⟧ in the type of the constructor ⟨_⟩ in the
  -- definition of μ.
