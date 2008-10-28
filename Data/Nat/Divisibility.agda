------------------------------------------------------------------------
-- Divisibility
------------------------------------------------------------------------

module Data.Nat.Divisibility where

open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
import Data.Fin as Fin
open Fin using (Fin; zero; suc; #_)
import Data.Fin.Props as FP
open import Data.Vec
open SemiringSolver
open import Algebra
private
  module CS = CommutativeSemiring commutativeSemiring
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Function

-- m Divides n is inhabited iff m is non-zero and divides n. (The
-- requirement that m should be non-zero follows MathWorld, which
-- follows Hardy and Wright's "An Introduction to the Theory of
-- Numbers".)

data _Divides_ : ℕ -> ℕ -> Set where
  divides : {m n : ℕ} (q : ℕ) (eq : n ≡ q * suc m) -> suc m Divides n

-- Extracts the quotient.

quotient : forall {m n} -> m Divides n -> ℕ
quotient (divides q _) = q

-- d Divides m And n means that d is a common divisor of m and n.

_Divides_And_ : (d m n : ℕ) -> Set
d Divides m And n = d Divides m × d Divides n

-- The divisibility relation is reflexive for positive integers.

divides-refl : forall n -> suc n Divides suc n
divides-refl n = divides 1 (≡-sym $ proj₁ CS.*-identity (suc n))

-- 1 divides everything.

1-divides_ : forall n -> 1 Divides n
1-divides n = divides n (≡-sym $ proj₂ CS.*-identity n)

-- Every positive integer divides 0.

_+1-divides-0 : forall n -> suc n Divides 0
n +1-divides-0 = divides 0 ≡-refl

-- 0 divides nothing.

0-doesNotDivide : forall {n} -> ¬ 0 Divides n
0-doesNotDivide ()

-- If m divides n, and n is positive, then m ≤ n.

divides-≤ : forall {m n} -> m Divides suc n -> m ≤ suc n
divides-≤             (divides 0       ())
divides-≤ {suc m} {n} (divides (suc q) eq) = begin
  suc m
    ≤⟨ m≤m+n (suc m) (q * suc m) ⟩
  suc q * suc m
    ≡⟨ ≡-sym eq ⟩
  suc n
    ∎
  where open ≤-Reasoning

-- If m and n divide each other, then they are equal.

divides-≡ : forall {m n} -> m Divides n -> n Divides m -> m ≡ n
divides-≡ (divides a₁ b₁) (divides a₂ b₂) =
  ≤≥⇒≡ (divides-≤ (divides a₁ b₁)) (divides-≤ (divides a₂ b₂))

-- If i divides m and n, then i divides their sum.

divides-+ : forall {i m n} ->
            i Divides m -> i Divides n -> i Divides (m + n)
divides-+ (divides {m = i} q ≡-refl) (divides q' ≡-refl) =
  divides (q + q') (≡-sym $ proj₂ CS.distrib (suc i) q q')

-- If i divides m and n, then i divides their difference.

divides-∸ : forall {i m n} ->
            i Divides (m + n) -> i Divides m -> i Divides n
divides-∸ (divides {m = i} q' eq) (divides q ≡-refl) =
  divides (q' ∸ q)
          (≡-sym $ im≡jm+n⇒[i∸j]m≡n q' q (suc i) _ $ ≡-sym eq)

-- If i divides i + n then i divides n.

divides-Δ : forall {i n} -> i Divides (i + n) -> i Divides n
divides-Δ {suc i} d  = divides-∸ d (divides-refl i)
divides-Δ {zero}  ()

-- If the remainder after division is non-zero, then the divisor does
-- not divide the dividend.

nonZeroDivisor-lemma
  : forall m q (r : Fin (1 + m)) -> Fin.toℕ r ≢ 0 ->
    ¬ (1 + m) Divides (Fin.toℕ r + q * (1 + m))
nonZeroDivisor-lemma m zero r r≢zero (divides zero eq) = r≢zero $ begin
  Fin.toℕ r
    ≡⟨ ≡-sym $ proj₁ CS.*-identity (Fin.toℕ r) ⟩
  1 * Fin.toℕ r
    ≡⟨ eq ⟩
  0
    ∎
  where open ≡-Reasoning
nonZeroDivisor-lemma m zero r r≢zero (divides (suc q) eq) =
  ¬i+1+j≤i m $ begin
    m + suc (q * suc m)
      ≡⟨ (let M = var (# 0); Q = var (# 1) in
          prove (m ∷ q * suc m ∷ [])
                (M :+ (con 1 :+ Q)) (con 1 :+ M :+ Q) ≡-refl) ⟩
    suc (m + q * suc m)
      ≡⟨ ≡-sym eq ⟩
    1 * Fin.toℕ r
      ≡⟨ proj₁ CS.*-identity (Fin.toℕ r) ⟩
    Fin.toℕ r
      ≤⟨ ≤-pred $ FP.bounded r ⟩
    m
      ∎
  where open ≤-Reasoning
nonZeroDivisor-lemma m (suc q) r r≢zero d =
  nonZeroDivisor-lemma m q r r≢zero (divides-Δ d')
  where
  lem = prove (suc m ∷ Fin.toℕ r ∷ q * suc m ∷ [])
              (R :+ (M :+ Q)) (M :+ (R :+ Q))
              ≡-refl
    where M = var (# 0); R = var (# 1); Q = var (# 2)
  d' = ≡-subst (\x -> (1 + m) Divides x) lem d

-- Divisibility is decidable.

divisible? : Decidable _Divides_
divisible? zero    n                            = no 0-doesNotDivide
divisible? (suc m) n                            with n divMod suc m
divisible? (suc m) .(q * suc m)                 | result q zero    =
  yes $ divides q ≡-refl
divisible? (suc m) .(1 + Fin.toℕ r + q * suc m) | result q (suc r) =
  no $ nonZeroDivisor-lemma m q (suc r) (\())
