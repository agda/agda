{-# OPTIONS --with-K #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

single : {m n : Nat} → suc m ≡ suc n → n ≡ m
single p invert refl ← p = refl

double : {m n p : Nat} → suc m ≡ n → suc n ≡ 2 + p → m ≡ p
double p q invert refl ← p | refl ← q = refl

_∋_ : (A : Set) → A → A
A ∋ a = a

-- The second equality proof is only well-typed
-- after the first one has been used

tele : {m n : Nat} → suc m ≡ suc n → m ≡ n
tele {m} {n} p invert refl ← p | refl ← (n ≡ m) ∋ refl = refl

tele' : {m n : Nat} → m ≡ n → m ≡ n
tele' {m} {n} p invert refl ← p with (n ≡ m) ∋ refl
... | q = refl

-- Further splitting after a using & with

tele'' : {m n : Nat} → m ≡ n → Nat → Nat
tele'' {m} {n} p r invert refl ← p with (n ≡ m) ∋ refl
tele'' {m} {m} p zero    | q = m
tele'' {m} {m} p (suc r) | q = r

data Vec : Nat → Set where
  []  : Vec 0
  _∷_ : ∀ {n} → Nat → Vec n → Vec (suc n)

head : ∀ {n} → Vec (suc n) → Nat
head xs invert (x ∷ _) ← xs = x

castVec : ∀ {m n} → m ≡ n → Vec m → Vec n
castVec eq ms invert refl ← eq = ms

data All (P : Nat → Set) : ∀ {n} → Vec n → Set where
  []  : All P []
  _∷_ : ∀ {n x} {xs : Vec n} → P x → All P xs → All P (x ∷ xs)

open import Agda.Builtin.Sigma

castAll : ∀ {P m n xs ys} → Σ (m ≡ n) (λ eq → castVec eq xs ≡ ys) →
          All P xs → All P ys
castAll eq all invert (refl , refl) ← eq = all
