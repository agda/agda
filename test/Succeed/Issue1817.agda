-- Andreas, 2017-01-20, issue #1817 is fixed

{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Size
open import Agda.Builtin.Nat renaming (Nat to ℕ)

-- Function

_$_ : ∀{a b}{A : Set a}{B : Set b} →(A → B) → A →  B
f $ x = f x

case_of_ : ∀{a b}{A : Set a}{B : Set b} → A → (A → B) → B
case x of f = f x

-- Size

data SizeLt (i : Size) : Set where
  size : (j : Size< i) → SizeLt i

getSize : ∀{i} → SizeLt i → Size
getSize (size j) = j

-- List

data List (A : Set) : Set where
  [] : List A
  _∷_ : (x : A) (xs : List A) → List A

for : ∀{A B} (xs : List A) (f : A → B) → List B
for [] f = []
for (x ∷ xs) f = f x ∷ for xs f

-- BT

data Var : (n : ℕ) → Set where
  vz : ∀{n} → Var (suc n)
  vs : ∀{n} → (x : Var n) → Var (suc n)

mutual
  record BT (i : Size) (n : ℕ) : Set where
    inductive; constructor Λ
    field nabs : ℕ
          var  : Var (nabs + n)
          args : List (BT' i (nabs + n))

  record BT' (i : Size) (n : ℕ) : Set where
    coinductive; constructor delay
    field force : ∀{j : SizeLt i} → BT (getSize j) n

open BT'

-- Renaming

data Ope : (n m : ℕ) → Set where
  id   : ∀{n} → Ope n n
  weak : ∀{n m} (ρ : Ope n m) → Ope (1 + n) m
  lift : ∀{n m} (ρ : Ope n m) → Ope (1 + n) (1 + m)

lifts : ∀ k {n m} (ρ : Ope n m) → Ope (k + n) (k + m)
lifts 0       ρ = ρ
lifts (suc k) ρ = lift (lifts k ρ)

renVar : ∀{n m} (ρ : Ope n m) (x : Var m) → Var n
renVar id       x      = x
renVar (weak ρ) x      = vs (renVar ρ x)
renVar (lift ρ) vz     = vz
renVar (lift ρ) (vs x) = vs (renVar ρ x)

ren  : ∀{i n m} (ρ : Ope n m) (t : BT i m) → BT i n
ren {i} ρ₀ (Λ n x ts) = Λ n (renVar ρ x) $ for ts \ t → delay
   \{ {size j} → ren {j} ρ $ force t {size j} }
  where ρ = lifts n ρ₀
