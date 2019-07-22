{-# OPTIONS --with-K #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

single : {m n : Nat} → suc m ≡ suc n → n ≡ m
single p with refl ← p = refl

double : {m n p : Nat} → suc m ≡ n → suc n ≡ 2 + p → m ≡ p
double p q with refl ← p | refl ← q = refl

_∋_ : (A : Set) → A → A
A ∋ a = a

-- The second equality proof is only well-typed
-- after the first one has been used

tele : {m n : Nat} → suc m ≡ suc n → m ≡ n
tele {m} {n} p
  with refl ← p
       | refl ← (n ≡ m) ∋ refl
       = refl

tele' : {m n : Nat} → m ≡ n → m ≡ n
tele' {m} {n} p with refl ← p with (n ≡ m) ∋ refl
... | q = refl

-- Further splitting after a using & with

tele'' : {m n : Nat} → m ≡ n → Nat → Nat
tele'' {m} {n} p r with refl ← p | (n ≡ m) ∋ refl
tele'' {m} {m} p zero    | q = m
tele'' {m} {m} p (suc r) | q = r

data Vec {a} (A : Set a) : Nat → Set a where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

module _ {a} {A : Set a} {n} (xs : Vec A (suc n)) where

  head : A
  head with (x ∷ _) ← xs = x

  tail : Vec A n
  tail with (_ ∷ xs) ← xs = xs -- pattern shadows variable with'd on

castVec : ∀ {m n} → m ≡ n → Vec Nat m → Vec Nat n
castVec eq ms with refl ← eq = ms

data All (P : Nat → Set) : ∀ {n} → Vec Nat n → Set where
  []  : All P []
  _∷_ : ∀ {n x xs} → P x → All P {n} xs → All P (x ∷ xs)

open import Agda.Builtin.Sigma

castAll : ∀ {P m n xs ys} → Σ (m ≡ n) (λ eq → castVec eq xs ≡ ys) →
          All P xs → All P ys
castAll (refl , refl) all = all
