{-# OPTIONS --rewriting #-}

module RewritingNat where

open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero + n = n
(suc m) + n = suc (m + n)

plus0T : Set
plus0T = ∀{x} → (x + zero) ≡ x

plusSucT : Set
plusSucT = ∀{x y} → (x + (suc y)) ≡ suc (x + y)

postulate
  plus0p : plus0T
  {-# REWRITE plus0p #-}

  plusSucp : plusSucT

{-# REWRITE plusSucp #-}

plus0 : plus0T
plus0 = refl

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

reverseAcc : ∀{A n m} → Vec A n → Vec A m → Vec A (n + m)
reverseAcc [] acc = acc
reverseAcc (x ∷ xs) acc = reverseAcc xs (x ∷ acc)
