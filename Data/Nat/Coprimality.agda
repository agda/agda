------------------------------------------------------------------------
-- Coprimality
------------------------------------------------------------------------

module Data.Nat.Coprimality where

open import Data.Nat
open import Data.Nat.Divisibility
open import Data.Nat.GCD
open import Logic
open import Data.Product
open import Data.Function

-- Coprime m n is inhabited iff m and n are coprime (relatively
-- prime), i.e. if their only common positive divisor is 1.

Coprime : (m n : ℕ) -> Set
Coprime m n = forall {i} -> suc i Divides m And n -> suc i ≡ 1

-- Coprime numbers have 1 as their GCD (unless they are both zero).

coprime-gcd : forall {m n} ->
              Coprime m n -> ¬ (m ≡ 0 × n ≡ 0) -> GCD m n 1
coprime-gcd {m} {n} c mn≢0 = isGCD (1-divides m , 1-divides n) (div _)
  where
  div : forall d -> d Divides m And n -> d Divides 1
  div (suc d)     cd        with c cd
  div (suc .zero) cd        | ≡-refl = 1-divides 1
  div zero        (d₁ , d₂) =
    ⊥-elim (mn≢0 (0-dividesOnly-0 d₁ , 0-dividesOnly-0 d₂))

-- If two numbers have 1 as their GCD, then they are coprime (unless
-- they are both zero).

gcd-coprime : forall {m n} ->
              GCD m n 1 -> ¬ (m ≡ 0 × n ≡ 0) -> Coprime m n
gcd-coprime g mn≢0  {i} cd with gcd-largest g mn≢0 cd
gcd-coprime g mn≢0 .{0} cd | s≤s z≤n = ≡-refl

-- The coprimality relation is symmetric.

coprime-sym : forall {m n} -> Coprime m n -> Coprime n m
coprime-sym c = c ∘ swap

-- Everything is coprime to 1.

1-coprimeTo : forall m -> Coprime 1 m
1-coprimeTo m = c _ ∘ proj₁
  where
  c : forall i -> suc i Divides 1 -> suc i ≡ 1
  c zero    _                    = ≡-refl
  c (suc _) (divides zero    ())
  c (suc _) (divides (suc _) ())

-- Nothing is coprime to 0, except for 1.

0-coprimeTo-1 : forall {m} -> Coprime 0 m -> m ≡ 1
0-coprimeTo-1 {1}           _ = ≡-refl
0-coprimeTo-1 {zero}        c with c (2 divides-0 , 2 divides-0)
... | ()
0-coprimeTo-1 {suc (suc m)} c with c ( (2 + m) divides-0
                                     , divides-refl (2 + m) )
... | ()

-- If m and n are coprime, then n + m and n are also coprime.

coprime-+ : forall {m n} -> Coprime m n -> Coprime (n + m) n
coprime-+ {m = zero} {n}           c with 0-coprimeTo-1 c
coprime-+ {m = zero} {1}           c | ≡-refl = 1-coprimeTo 1
coprime-+ {m = zero} {zero}        c | ()
coprime-+ {m = zero} {suc (suc _)} c | ()
coprime-+ {m = suc _}              c =
  \d -> c (divides-∸ (proj₁ d) (proj₂ d) , proj₂ d)
