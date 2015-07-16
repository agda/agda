-- Andreas, 2015-07-16, issue reported by Nisse

postulate
  A   : Set₁
  P   : A → Set₁
  T   : Set₁ → Set₁
  Σ   : (A : Set₁) → (A → Set₁) → Set₁
  T-Σ : {A : Set₁} {B : A → Set₁} → (∀ x → T (B x)) → T (Σ A B)

t : T (Σ Set λ _ → Σ (A → A) λ f → Σ (∀ x₁ → P (f x₁)) λ _ → Set)
t = T-Σ λ _ → T-Σ λ _ → T-Σ {!!}

-- WAS:
-- Goal type and context:
--
--   Goal: (x : (x₁ : A) → P (x₁ x₁)) → T Set
--   ————————————————————————————————————————————————————————————
--   x₁ : A → A
--   x  : Set
--
-- Note the application "x₁ x₁".

-- EXPECTED:
-- Goal: (x : (x₁ : A) → P (.x₁ x₁)) → T Set
-- ————————————————————————————————————————————————————————————
-- .x₁ : A → A
-- .x  : Set


id : (x : A) → A
-- id _ = {!!}      -- Context displays .x
id = λ _ → {!!}  -- Context should display .x
