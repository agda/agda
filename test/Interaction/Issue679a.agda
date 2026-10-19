module Issue679a where

data ty : Set where
  _`→_ : ty → ty → ty

⟦_⟧ : ty → Set
⟦ A `→ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧

eq : ∀ (σ : ty) (a b : ⟦ σ ⟧) → Set
eq (A `→ B) f g = ∀ {a : ⟦ A ⟧} → eq B (f a) (g a)

eq-sym : ∀ σ {f g} (h : eq σ f g) → eq σ g f
eq-sym (A `→ B) h with B
... | B' = {!!}
