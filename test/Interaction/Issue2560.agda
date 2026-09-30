open import Agda.Builtin.Nat

postulate Pos : Set

data FVec : (n : Nat) → Set₁ where
  FNil  : FVec 0
  FCons : ∀ {n} → (Pos → Set) → FVec (suc n)

pre : ∀ {m n} → FVec m → FVec (suc n) → Pos → Set
pre FNil      (FCons x) = x
pre (FCons x) _         = x

data proofAG : ∀ {n} → FVec n → Set where
  []AG : proofAG FNil

postulate
  preAG : ∀ m n (v : FVec m) (v' : FVec (suc n)) →
            proofAG v → proofAG v' → ∀ p → pre v v' p
  m n : Nat
  v  : FVec m
  v' : FVec (suc n)
  p  : Pos

preAG₁ : pre v v' p
preAG₁ = preAG 0 n FNil _ []AG {!!} p
  -- Refine gives internal error instead of 'Cannot refine' or
  -- 'No introduction forms found'.

postulate Constrain : (A B : Set) → (A → B) → Set
syntax Constrain A B (λ x → y) = x ∈ A => y ∈ B

preAG₂ : (let X : FVec (suc n)
              X = _) →
         x ∈ pre FNil X p => x ∈ pre v v' p →
         proofAG X → Set
preAG₂ _ p = {!p!}
  -- Splitting on p causes the same internal error.
