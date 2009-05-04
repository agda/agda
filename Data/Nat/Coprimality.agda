------------------------------------------------------------------------
-- Coprimality
------------------------------------------------------------------------

module Data.Nat.Coprimality where

open import Data.Nat
import Data.Nat.Properties as NatProp
open import Data.Nat.Divisibility as Div
open import Data.Nat.GCD
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
Coprime m n = ∀ {i} → i ∣ m × i ∣ n → i ≡ 1

-- Coprime numbers have 1 as their gcd.

coprime-gcd : ∀ {m n} → Coprime m n → GCD m n 1
coprime-gcd {m} {n} c = GCD.is (1∣ m , 1∣ n) greatest
  where
  greatest : ∀ {d} → d ∣ m × d ∣ n → d ∣ 1
  greatest      cd with c cd
  greatest .{1} cd | refl = 1∣ 1

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
1-coprimeTo m = 1∣1 ∘ proj₁

-- Nothing except for 1 is coprime to 0.

0-coprimeTo-1 : ∀ {m} → Coprime 0 m → m ≡ 1
0-coprimeTo-1 {m} c = c (m ∣0 , P.refl)

-- If m and n are coprime, then n + m and n are also coprime.

coprime-+ : ∀ {m n} → Coprime m n → Coprime (n + m) n
coprime-+ c (d₁ , d₂) = c (∣-∸ d₁ d₂ , d₂)
