
module Issue292-19 where

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

data P′ : ∀ i → D i → Set where
  p₁ : P′ i₁ d₁

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

Foo : ∀ {i} (d : D i) → P′ i d → Set₁
Foo d₁ _  = Set
Foo d₂ ()
