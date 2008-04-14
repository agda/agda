------------------------------------------------------------------------
-- Divisibility
------------------------------------------------------------------------

module Data.Nat.Divisibility where

open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.Fin
open import Data.Vec
open ℕ-semiringSolver
open import Algebra
private
  module CS = CommutativeSemiring ℕ-commutativeSemiring
open import Data.Product
open import Logic
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Function

-- m Divides n is inhabited iff m divides n. (Note that the definition
-- does not require the numbers to be positive.)

data _Divides_ (m n : ℕ) : Set where
  divides : (q : ℕ) -> n ≡ q * m -> m Divides n

-- Extracts the quotient.

quotient : forall {m n} -> m Divides n -> ℕ
quotient (divides q _) = q

-- CommonDivisor d m n means that d divides both m and n.

data CommonDivisor (d m n : ℕ) : Set where
  commonDivisor : d Divides m -> d Divides n -> CommonDivisor d m n

-- The divisibility relation is reflexive.

divides-refl : forall n -> n Divides n
divides-refl n = divides 1 (≡-sym $ proj₁ CS.*-identity n)

-- Everything divides 0.

_divides-0 : forall n -> n Divides 0
n divides-0 = divides 0 ≡-refl

-- If 0 divides n, then n is 0.

0-dividesOnly-0 : forall {n} -> 0 Divides n -> n ≡ 0
0-dividesOnly-0 {n} (divides q eq) = begin
  n
    ≡⟨ eq ⟩
  q * 0
    ≡⟨ proj₂ CS.zero q ⟩
  0
    ∎
  where open ≡-Reasoning

-- If m divides n, and n is positive, then m ≤ n.

divides-≤ : forall {m n} -> m Divides suc n -> m ≤ suc n
divides-≤ {m = zero}  _                        = z≤n  -- Impossible.
divides-≤             (divides zero    ())
divides-≤ {m = suc m} (divides (suc q) ≡-refl) = m≤m+n (suc m) (q * suc m)

-- If m and n divide each other, then they are equal.

divides-≡ : forall {m n} -> m Divides n -> n Divides m -> m ≡ n
divides-≡ {m = 0}         d  _  = ≡-sym $ 0-dividesOnly-0 d
divides-≡ {n = 0}         _  d  = 0-dividesOnly-0 d
divides-≡ {suc m} {suc n} d₁ d₂ = ≤≥⇒≡ (divides-≤ d₁) (divides-≤ d₂)

-- If i divides m and m + n, then i divides n.

divides-+ : forall {i m n} ->
            i Divides m -> i Divides (m + n) -> i Divides n
divides-+ {i} (divides q ≡-refl) (divides q' eq) =
  divides (q' ∸ q) (≡-sym $ im≡jm+n⇒[i∸j]m≡n q' q i _ $ ≡-sym eq)

-- If i divides i + n, then i divides n.

divides-∸ : forall {i n} -> i Divides (i + n) -> i Divides n
divides-∸ {i} (divides zero    eq) = divides 0 (i+j≡0⇒j≡0 i eq)
divides-∸ {i} (divides (suc q) eq) = divides q (i+j≡i+k⇒j≡k i eq)

-- If the remainder after division is non-zero, then the divisor does
-- not divide the dividend.

nonZeroDivisor-lemma
  : forall m q (r : Fin (1 + m)) -> toℕ r ≢ 0 ->
    ¬ (1 + m) Divides (toℕ r + q * (1 + m))
nonZeroDivisor-lemma m zero r r≢fz (divides zero eq) = r≢fz $ begin
  toℕ r
    ≡⟨ ≡-sym $ proj₁ CS.*-identity (toℕ r) ⟩
  1 * toℕ r
    ≡⟨ eq ⟩
  0
    ∎
  where open ≡-Reasoning
nonZeroDivisor-lemma m zero r r≢fz (divides (suc q) eq) =
  ¬i+1+j≤i m $ begin
    m + suc (q * suc m)
      ≡⟨ (let M = var fz; Q = var (fs fz) in
          prove (m ∷ q * suc m ∷ [])
                (M :+ (con 1 :+ Q)) (con 1 :+ M :+ Q) ≡-refl) ⟩
    suc (m + q * suc m)
      ≡⟨ ≡-sym eq ⟩
    1 * toℕ r
      ≡⟨ proj₁ CS.*-identity (toℕ r) ⟩
    toℕ r
      ≤⟨ ≤-pred $ Fin-bounded r ⟩
    m
      ∎
  where open ≤-Reasoning
nonZeroDivisor-lemma m (suc q) r r≢fz d =
  nonZeroDivisor-lemma m q r r≢fz (divides-∸ d')
  where
  lem = prove (suc m ∷ toℕ r ∷ q * suc m ∷ [])
              (R :+ (M :+ Q)) (M :+ (R :+ Q))
              ≡-refl
    where M = var fz; R = var (fs fz); Q = var (fs (fs fz))
  d' = ≡-subst (\x -> (1 + m) Divides x) lem d

-- Divisibility is decidable.

divisible? : Decidable _Divides_
divisible? zero    zero    = yes $ 0 divides-0
divisible? zero    (suc n) = no  $ zero≢suc ∘ ≡-sym ∘ 0-dividesOnly-0
divisible? (suc m) n                        with n divMod suc m
divisible? (suc m) .(q * suc m)             | result q fz     =
  yes $ divides q ≡-refl
divisible? (suc m) .(1 + toℕ r + q * suc m) | result q (fs r) =
  no $ nonZeroDivisor-lemma m q (fs r) (zero≢suc ∘ ≡-sym)
