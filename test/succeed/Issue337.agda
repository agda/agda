-- DontCares shouldn't end up in the generated with functions.
module Issue337 where

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

postulate
  _≤_ : ℕ → ℕ → Set
  p₁  : 0 ≤ 1
  p₂  : 0 ≤ 1

data SList (bound : ℕ) : Set where
  []    : SList bound
  scons : (head : ℕ) →
          .(head ≤ bound) →
          (tail : SList head) →
          SList bound

l₁ : SList 1
l₁ = scons 0 p₁ []

l₂ : SList 1
l₂ = scons 0 p₂ []

l₁≡l₂ : l₁ ≡ l₂
l₁≡l₂ with Set
... | _ = refl
