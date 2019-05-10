{-# OPTIONS --rewriting --confluence-check #-}

data Unit : Set where
  unit : Unit

_+_ : Unit → Unit → Unit
unit + x = x

data _≡_ (x : Unit) : Unit → Set where
  refl : x ≡ x

{-# BUILTIN REWRITE _≡_ #-}

postulate
  f  : Unit → Unit
  fu : f unit ≡ unit

{-# REWRITE fu #-}

g : Unit → Unit
g unit = unit

data D (h : Unit → Unit) (x : Unit) : Set where
  wrap : Unit → D h x

run : ∀ {h x} → D h x → Unit
run (wrap x) = x

postulate
  d₁ : ∀ n x y (p : D y n) → x (run p + n) ≡ y (run p + n) → D x n

d₂ : ∀ s n → D s n
d₂ _ _ = wrap unit

d₃ : D (λ _ → unit) unit
d₃ = d₁ _ (λ _ → unit) (λ n → f (g n)) (d₂ (λ n → f (g n)) _) refl
