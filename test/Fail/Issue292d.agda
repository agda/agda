
module Issue292d where

postulate
  I     : Set
  i₁ i₂ : I
  J     : Set
  j     : I → J

data D : I → Set where
  d₁ : D i₁
  d₂ : D i₂

data P : ∀ i → D i → Set where
  p₁ : P i₁ d₁
  p₂ : P i₂ d₂

data E : J → Set where
  e₁ : E (j i₁)
  e₂ : E (j i₂)

data Q : ∀ i → E i → Set where
  q₁ : Q (j i₁) e₁
  q₂ : Q (j i₂) e₂

Ok : Q (j i₁) e₁ → Set₁
Ok q₁ = Set

AlsoOk : P i₁ d₁ → Set₁
AlsoOk p₁ = Set

Bad : D i₁ → Set₁
Bad d₁ = Set
