-- Separate cofibrations (constraints) from interval expressions

-- Spinning ideas...
-- Christian Sattler and Andreas Abel, 2022-05-31

{-# BUILTIN INTERVAL-CONSTRAINT F #-} -- new universe F : SSet₀

postulate
  IEq : I → I → F

{-# BUILTIN INTERVAL-EQ IEq #-}

-- Closed under Pi and Sigma
-- I : IUniv , B : I → F  ⊢  (i : I) → B i : F
-- A : F     , B : A → F  ⊢  Σ A B : F

-- Definitionally proof-irrelevant
--
-- A : F , x y : A ⊢ x = y : A

-- Disjunction
--
-- primFOr : F → F → F
--
-- primFFalse : F

-- What are the restrictions when defining data types in F?
-- What are the extra conditions when pattern matching on such a data type?

primitive
  data FOr (ϕ ψ : F) : F where
    injF₁ (x : ϕ) : FOr ϕ ψ
    injF₂ (y : ψ) : FOr ϕ ψ

-- ACI (associative - commutative - idempotent)

-- Strict Propositional Extensionality of F

-- Γ ⊢ ϕ ≤ ψ : F  -- ϕ implies ψ
-- Γ ⊢ ψ ≤ ϕ : F
-- -------------
-- Γ ⊢ ϕ = ψ : F


-- Partial : ∀{ℓ} (ϕ : F) (A : Set ℓ) → Set ℓ
-- Partial ϕ A = ϕ → A

primitive
  primPOr : ∀ {ℓ} (ϕ ψ : Φ) {A : primFOr ϕ ψ → (Set ℓ)}
            → (u : (x : ϕ) → A (injF₁ x))
            → (v : (y : ψ) → A (injF₂ y))
            → (z : primFOr ϕ ψ) → A z

-- Side condition
-- x : ϕ, y : ψ |- u x = v y : A (injF₁ x)


--  Γ ⊢ ℓ : Level
--  Γ ⊢ ϕ ψ : F
--  Γ , z : primFOr ϕ ψ ⊢ A : Set ℓ
--  Γ , x : ϕ ⊢ u : A[injF₁ x]
--  Γ , y : ψ ⊢ v : A[injF₂ y]
--  Γ , x : ϕ, y : ψ ⊢ u x = v y : A[injF₁ x]
--  --------------------------------------------
--  Γ ⊢ λ{ (injF₁ x) → u; (injF₂ y) → v } : (z : primFOr ϕ ψ) → A z
--
--  How to write/check systems?
--
--  Γ ⊢ ℓ : Level
--  Γ ⊢ ϕ₁ ... ϕₙ : F
--  Γ , z : ϕ₁ ∨ ... ∨ ϕₙ ⊢ A : Set ℓ
--  Γ , x₁ : ϕ₁ ⊢ u₁ : A[injF₁ x₁]
--  ...
--  Γ , xₙ : ϕₙ ⊢ uₙ : A[injFₙ xₙ]
--  Γ , x : ϕᵢ, y : ϕⱼ ⊢ uᵢ x = uⱼ y : A[injFᵢ x]  for all i,j
--  ----------------------------------------------------------
--  Γ ⊢ λ{ ϕ₁ → u₁ ... ϕₙ → uₙ } : (z : ϕ₁ ∨ ... ∨ ϕₙ) → A z


-- fFalseElim : IEq i0 i1 → {a} (A : Set a) → A


Constraints should resolve to substitutions.
