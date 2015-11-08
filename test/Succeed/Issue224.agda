
module Issue224 where

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

data D (A : Set) : Maybe A → Set where
  d₁ : (x : A) → D A (just x)
  d₂ : ∀ {x} → D A x → D A x

data S : ∀ {A x} → D A x → Set₁ where
  s : ∀ {A x} {d : D A x} → S d → S (d₂ d)

foo : {A : Set} → S (d₂ (d₁ (nothing {A}))) → Set₁
foo (s _) = Set

-- Bug.agda:19,6-9
-- Panic: Pattern match failure in do expression at
-- src/full/Agda/TypeChecking/Rules/LHS/Unify.hs:331:2-5
-- when checking that the pattern s _ has type S (d₂ (d₁ nothing))
