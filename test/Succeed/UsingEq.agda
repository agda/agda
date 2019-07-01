{-# OPTIONS --with-K #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

single : {m n : Nat} → suc m ≡ suc n → n ≡ m
single p using p = refl

--

double : {m n p : Nat} → suc m ≡ n → suc n ≡ 2 + p → m ≡ p
double p q using p | q = refl

_∋_ : (A : Set) → A → A
A ∋ a = a

-- The second equality proof is only well-typed
-- after the first one has been used

tele : {m n : Nat} → suc m ≡ suc n → m ≡ n
tele {m} {n} p using p | (n ≡ m) ∋ refl = refl

tele' : {m n : Nat} → m ≡ n → m ≡ n
tele' {m} {n} p using p with (n ≡ m) ∋ refl
... | q = refl

-- Further splitting after a using & with

tele'' : {m n : Nat} → m ≡ n → Nat → Nat
tele'' {m} {n} p r using p with (n ≡ m) ∋ refl
tele'' {m} {m} p zero    | q = m
tele'' {m} {m} p (suc r) | q = r
