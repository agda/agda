-- Andreas, 2026-10-06, issue #8811
-- The occurs check should not impose modality restrictions on the
-- sort annotation of a type, since the type checker does not either.
-- Here, ℓ only occurs in the sort annotation of the domain A in A → A.

{-# OPTIONS --polarity --experimental-irrelevance #-}

open import Agda.Primitive

-- If a definition is accepted, giving it interactively should also succeed.

-- Polarity version.

F₀ : (@unused ℓ : Level) (A : Set ℓ) → Set ℓ
F₀ ℓ A = A → A

F : (@unused ℓ : Level) (A : Set ℓ) → Set ℓ
F ℓ A = {! A → A !}  -- Giving "A → A" should succeed.

-- Relevance version.

G₀ : .(ℓ : Level) (A : Set ℓ) → Set ℓ
G₀ ℓ A = A → A

G : .(ℓ : Level) (A : Set ℓ) → Set ℓ
G ℓ A = {! A → A !}  -- Giving "A → A" should succeed.
