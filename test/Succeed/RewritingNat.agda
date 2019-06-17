{-# OPTIONS --rewriting --confluence-check #-}

module RewritingNat where

open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero + n = n
(suc m) + n = suc (m + n)

plusAssoc : ∀ x {y z : Nat} → ((x + y) + z) ≡ (x + (y + z))
plusAssoc zero = refl
plusAssoc (suc x) {y} {z} rewrite plusAssoc x {y} {z} = refl

plus0T : Set
plus0T = ∀{x} → (x + zero) ≡ x

plusSucT : Set
plusSucT = ∀{x y} → (x + (suc y)) ≡ suc (x + y)

postulate
  plus0p : plus0T
  {-# REWRITE plus0p #-}

  plusSucp : plusSucT

{-# REWRITE plusSucp plusAssoc #-}

plus0 : plus0T
plus0 = refl

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

-- Needs REWRITE plus0p plusSucp
reverseAcc : ∀{A n m} → Vec A n → Vec A m → Vec A (n + m)
reverseAcc [] acc = acc
reverseAcc (x ∷ xs) acc = reverseAcc xs (x ∷ acc)

append : ∀{A n m} → Vec A n → Vec A m → Vec A (n + m)
append []       ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

-- Note: appendAssoc needs REWRITE plusAssoc to be well-typed.
appendAssoc : ∀{A n m l} (u : Vec A n) {v : Vec A m}{w : Vec A l} →
  append (append u v) w ≡ append u (append v w)
appendAssoc [] = refl
appendAssoc (x ∷ xs) {v} {w} rewrite appendAssoc xs {v} {w} = refl
