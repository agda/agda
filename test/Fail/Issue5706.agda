-- Andreas, 2021-12-22, issue #5706 reported by Trebor-Huang
-- In Agda <= 2.6.2.1, Int overflow can be exploited.

-- Basically just a modified version of Russell's paradox found at
-- http://liamoc.net/posts/2015-09-10-girards-paradox.html.

-- -- This 64bit Int overflow got us Set:Set.
-- WTF : Set₀
-- WTF = Set₁₈₄₄₆₇₄₄₀₇₃₇₀₉₅₅₁₆₁₅
-- -- 18446744073709551615 = 2^64 - 1

-- Some preliminaries, just to avoid any library imports:

data _≡_ {ℓ : _} {A : Set ℓ} : A → A → Set where
    refl : ∀ {a} → a ≡ a

record ∃ {A : Set} (P : A → Set) : Set where
    constructor _,_
    field
        proj₁ : A
        proj₂ : P proj₁
open ∃

data ⊥ : Set where

-- The rest follows the linked development of Russell's paradox.

-- Naive sets (tree representation), accepted with --type-in-type.

data SET : Set where
  set : (X : Set₁₈₄₄₆₇₄₄₀₇₃₇₀₉₅₅₁₆₁₅) → (X → SET) → SET

-- Elementhood

_∈_ : SET → SET → Set
a ∈ set X f = ∃ λ x → a ≡ f x

_∉_ : SET → SET → Set
a ∉ b = (a ∈ b) → ⊥

-- The set Δ of sets that do not contain themselves.

Δ : SET
Δ = set (∃ λ s → s ∉ s) proj₁

-- Any member of Δ does not contain itself.

x∈Δ→x∉x : ∀ {X} → X ∈ Δ → X ∉ X
x∈Δ→x∉x ((Y , Y∉Y) , refl) = Y∉Y

-- Δ does not contain itself.

Δ∉Δ : Δ ∉ Δ
Δ∉Δ Δ∈Δ = x∈Δ→x∉x Δ∈Δ Δ∈Δ

-- Any set that does not contain itself lives in Δ.

x∉x→x∈Δ : ∀ {X} →  X ∉ X → X ∈ Δ
x∉x→x∈Δ {X} X∉X = (X , X∉X) , refl

-- So Δ must live in Δ, which is absurd.

falso : ⊥
falso = Δ∉Δ (x∉x→x∈Δ Δ∉Δ)
