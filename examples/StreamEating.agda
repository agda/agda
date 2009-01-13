module StreamEating where

codata ∞ (A : Set) : Set where
  ♯_ : (x : A) → ∞ A

♭ : ∀ {A} → ∞ A → A
♭ (♯ x) = x

-- Infinite streams.

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

-- A stream processor SP A B consumes elements of A and produces
-- elements of B. It can only consume a finite number of A's before
-- producing a B.

data SP (A B : Set) : Set where
  get : (f : A → SP A B) → SP A B
  put : (b : B) (sp : ∞ (SP A B)) → SP A B

eat : ∀ {A B} → SP A B → Stream A → Stream B
eat (get f)    (a ∷ as) = eat (f a) (♭ as)
eat (put b sp) as       = b ∷ rec where rec ~ ♯ eat (♭ sp) as

_∘_ : ∀ {A B C} → SP B C → SP A B → SP A C
get f₁    ∘ put x sp₂ = f₁ x ∘ ♭ sp₂
put x sp₁ ∘ sp₂       = put x rec where rec ~ ♯ (♭ sp₁ ∘ sp₂)
sp₁       ∘ get f₂    = get (λ x → sp₁ ∘ f₂ x)
