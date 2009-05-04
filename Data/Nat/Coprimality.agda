------------------------------------------------------------------------
-- Coprimality
------------------------------------------------------------------------

module Data.Nat.Coprimality where

open import Data.Nat
import Data.Nat.Properties as NatProp
open import Data.Nat.Divisibility as Div
open import Data.Nat.GCD hiding (refl; sym)
open import Data.Product
open import Data.Function
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)
open import Relation.Binary
private
  module P = Poset Div.poset

-- Coprime m n is inhabited iff m and n are coprime (relatively
-- prime), i.e. if their only common divisor is 1.

Coprime : (m n : ℕ) → Set
Coprime m n = ∀ {i} → i Divides m And n → i ≡ 1

-- Coprime numbers have 1 as their gcd.

coprime-gcd : ∀ {m n} → Coprime m n → GCD m n 1
coprime-gcd {m} {n} c = isGCD (1-divides m , 1-divides n) (div _)
  where
  div : ∀ d → d Divides m And n → d Divides 1
  div  d cd with c cd
  div .1 cd | refl = 1-divides 1

-- If two numbers have 1 as their gcd, then they are coprime.

gcd-coprime : ∀ {m n} → GCD m n 1 → Coprime m n
gcd-coprime g cd with GCD.greatest g cd
gcd-coprime g cd | divides q eq =
  NatProp.i*j≡1⇒j≡1 q _ (PropEq.sym eq)

-- The coprimality relation is symmetric.

sym : ∀ {m n} → Coprime m n → Coprime n m
sym c = c ∘ swap

-- Everything is coprime to 1.

1-coprimeTo : ∀ m → Coprime 1 m
1-coprimeTo m = c ∘ proj₁
  where
  c : ∀ {i} → i Divides 1 → i ≡ 1
  c {i} i∣1 = P.antisym i∣1 (1-divides i)

-- Nothing except for 1 is coprime to 0.

0-coprimeTo-1 : ∀ {m} → Coprime 0 m → m ≡ 1
0-coprimeTo-1 {m} c = c (m divides-0 , P.refl)

-- If m and n are coprime, then n + m and n are also coprime.

coprime-+ : ∀ {m n} → Coprime m n → Coprime (n + m) n
coprime-+ c (d₁ , d₂) = c (divides-∸ d₁ d₂ , d₂)
