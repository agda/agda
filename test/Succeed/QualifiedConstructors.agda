
module QualifiedConstructors where

data Nat₁ : Set where
  zero : Nat₁
  suc  : Nat₁ → Nat₁

data Nat₂ : Set where
  zero : Nat₂
  suc  : Nat₂ → Nat₂

zero₁ = Nat₁.zero
one₂  = Nat₂.suc Nat₂.zero

record Suc : Set where
  constructor suc
  field n : Nat₁

-- one₃ = Suc.suc zero₁  -- removed feature, see #4189

pred : Suc → Nat₁
pred s = Suc.n s

conv : Nat₂ → Nat₁
conv Nat₂.zero    = Nat₁.zero
conv (Nat₂.suc n) = Nat₁.suc (conv n)

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

inj : (n m : Nat₁) → Nat₁.suc n ≡ suc m → n ≡ m
inj .m m refl = refl
