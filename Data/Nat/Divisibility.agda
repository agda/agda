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

data _Divides_ : ℕ -> ℕ -> Set where
  divides : forall m q -> m Divides (q * m)

-- Extracts the quotient.

quotient : forall {m n} -> m Divides n -> ℕ
quotient (divides m q) = q

-- Pattern matching on _Divides_ can make life hard for the
-- completeness checker. In this case the following lemma is handy.

divides-lemma : forall {m n} (d : m Divides n) -> n ≡ quotient d * m
divides-lemma (divides m q) = ≡-refl

-- CommonDivisor d m n means that d divides both m and n.

data CommonDivisor (d m n : ℕ) : Set where
  commonDivisor : d Divides m -> d Divides n -> CommonDivisor d m n

-- The divisibility relation is reflexive.

divides-refl : forall n -> n Divides n
divides-refl n = ≡-subst (\x -> n Divides x) (proj₁ CS.*-identity n) $
                   divides n 1

-- Everything divides 0.

_divides-0 : forall n -> n Divides 0
n divides-0 = divides n 0

-- If 0 divides n, then n is 0.

0-dividesOnly-0 : forall {n} -> 0 Divides n -> n ≡ 0
0-dividesOnly-0 {n} d = begin
  n
    ≡⟨ divides-lemma d ⟩
  quotient d * 0
    ≡⟨ proj₂ CS.zero (quotient d) ⟩
  0
    ∎
  where open ≡-Reasoning

-- If m divides n, and n is positive, then m ≤ n.

divides-≤ : forall {m n} -> m Divides suc n -> m ≤ suc n
divides-≤ d = helper _ (quotient d) (divides-lemma d)
  where
  helper : forall m {n} q -> suc n ≡ q * m -> m ≤ suc n
  helper _       zero    ()
  helper zero    (suc q) _      = z≤n
  helper (suc m) (suc q) ≡-refl = m≤m+n (suc m) (q * suc m)

-- If m and n divide each other, then they are equal.

divides-≡ : forall {m n} -> m Divides n -> n Divides m -> m ≡ n
divides-≡ {m = 0}         d  _  = ≡-sym $ 0-dividesOnly-0 d
divides-≡ {n = 0}         _  d  = 0-dividesOnly-0 d
divides-≡ {suc m} {suc n} d₁ d₂ = ≤≥⇒≡ (divides-≤ d₁) (divides-≤ d₂)

-- If i divides m and m + n, then i divides n.

divides-+ : forall {i m n} ->
            i Divides m -> i Divides (m + n) -> i Divides n
divides-+ im imn = helper im imn ≡-refl
  where
  helper : forall {i j m n} ->
           i Divides m -> i Divides j -> j ≡ m + n ->
           i Divides n
  helper (divides i m) (divides .i j) eq =
    ≡-subst (\x -> i Divides x) (im≡jm+n⇒[i∸j]m≡n j m i _ eq) $
      divides i (j ∸ m)

-- If i divides i + n, then i divides n.

divides-∸ : forall {i n} -> i Divides (i + n) -> i Divides n
divides-∸ iin = helper iin ≡-refl
  where
  helper : forall {i j n} ->
           i Divides j -> j ≡ i + n -> i Divides n
  helper (divides i zero) eq =
    ≡-subst (\x -> i Divides x) (≡-sym $ i+j≡0⇒j≡0 i $ ≡-sym eq) $
      i divides-0
  helper (divides i (suc q)) eq with i+j≡i+k⇒j≡k i eq
  ... | ≡-refl = divides i q

-- If the remainder after division is non-zero, then the divisor does
-- not divide the dividend.

nonZeroDivisor-lemma
  : forall m q (r : Fin (1 + m)) -> toℕ r ≢ 0 ->
    ¬ (1 + m) Divides (toℕ r + q * (1 + m))
nonZeroDivisor-lemma m (suc q) r r≢fz d =
  nonZeroDivisor-lemma m q r r≢fz (divides-∸ d')
  where
  lem = prove (suc m ∷ toℕ r ∷ q * suc m ∷ [])
              (R :+ (M :+ Q)) (M :+ (R :+ Q))
              ≡-refl
    where M = var fz; R = var (fs fz); Q = var (fs (fs fz))
  d' = ≡-subst (\x -> (1 + m) Divides x) lem d
nonZeroDivisor-lemma m zero r r≢fz d =
  helper (quotient d) (toℕ r) r≢fz (≤-pred $ Fin-bounded r) eq
  where
  eq = begin
    toℕ r
      ≡⟨ ≡-sym $ proj₁ CS.*-identity (toℕ r) ⟩
    1 * toℕ r
      ≡⟨ divides-lemma d ⟩
    quotient d * suc m
      ∎
    where open ≡-Reasoning

  helper : forall q r -> r ≢ 0 -> r ≤ m -> r ≢ q * (1 + m)
  helper zero    r r≢0 r≤m eq = r≢0 eq
  helper (suc q) r r≢0 r≤m eq = ¬i+1+j≤i m $ begin
    m + suc (q * suc m)
      ≡⟨ (let M = var fz; Q = var (fs fz) in
          prove (m ∷ q * suc m ∷ [])
                (M :+ (con 1 :+ Q)) (con 1 :+ M :+ Q) ≡-refl) ⟩
    suc (m + q * suc m)
      ≡⟨ ≡-sym eq ⟩
    r
      ≤⟨ r≤m ⟩
    m
      ∎
    where open ≤-Reasoning

-- Divisibility is decidable.

divisible? : Decidable _Divides_
divisible? zero    zero    = yes $ 0 divides-0
divisible? zero    (suc n) = no  $ zero≢suc ∘ ≡-sym ∘ 0-dividesOnly-0
divisible? (suc m) n                        with n divMod suc m
divisible? (suc m) .(q * suc m)             | result q fz     =
  yes $ divides (suc m) q
divisible? (suc m) .(1 + toℕ r + q * suc m) | result q (fs r) =
  no $ nonZeroDivisor-lemma m q (fs r) (zero≢suc ∘ ≡-sym)
