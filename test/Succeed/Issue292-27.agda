
module Issue292-27 where

postulate A : Set

data D : Set → Set where
  d₁ : D A
  d₂ : D (A → A)

data P : (B : Set) → B → D B → Set₁ where
  p₁ : (x : A)     → P A       x d₁
  p₂ : (f : A → A) → P (A → A) f d₂

Foo : (x : A) → P A x d₁ → Set₁
Foo x (p₁ .x) = Set

-- Cannot decide whether there should be a case for the constructor
-- p₂, since the unification gets stuck on unifying the inferred
-- indices
--   [A → A, f, d₂]
-- with the expected indices
--   [A, x, d₁]
-- when checking the definition of Foo
