------------------------------------------------------------------------
-- Integer division
------------------------------------------------------------------------

module Data.Nat.DivMod where

open import Data.Nat
open import Data.Nat.Properties
open SemiringSolver
import Data.Fin as Fin
open Fin using (Fin; zero; suc; #_; toℕ; fromℕ)
import Data.Fin.Props as Fin
open import Induction.Nat
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Vec
open import Data.Function

------------------------------------------------------------------------
-- Some boring lemmas

private

  lem₁ : ∀ m k → _
  lem₁ m k = cong suc $ begin
    m
      ≡⟨ Fin.inject+-lemma m k ⟩
    toℕ (Fin.inject+ k (fromℕ m))
      ≡⟨ (let X = var (# 0) in
         prove (toℕ (Fin.inject+ k (fromℕ m)) ∷ [])
               X (X :+ con 0) refl) ⟩
    toℕ (Fin.inject+ k (fromℕ m)) + 0
      ∎

  lem₂ : ∀ n → _
  lem₂ n =
    let N = var (# 0) in
    prove (n ∷ []) (con 1 :+ N) (con 1 :+ (N :+ con 0)) refl

  lem₃ : ∀ n k q r eq → _
  lem₃ n k q r eq = begin
      suc n + k
        ≡⟨ (let N = var (# 0); K = var (# 1) in
            prove (n ∷ k ∷ [])
                  (con 1 :+ N :+ K) (N :+ (con 1 :+ K))
                  refl) ⟩
      n + suc k
        ≡⟨ cong (_+_ n) eq ⟩
      n + (toℕ r + q * n)
        ≡⟨ (let N = var (# 0); R = var (# 1); Q = var (# 2) in
            prove (n ∷ toℕ r ∷ q ∷ [])
                  (N :+ (R :+ Q :* N)) (R :+ (con 1 :+ Q) :* N)
                  refl) ⟩
      toℕ r + suc q * n
        ∎

------------------------------------------------------------------------
-- Division

-- A specification of integer division.

data DivMod : ℕ → ℕ → Set where
  result : {divisor : ℕ} (q : ℕ) (r : Fin divisor) →
           DivMod (toℕ r + q * divisor) divisor

-- Sometimes the following type is more usable; functions in indices
-- can be inconvenient.

data DivMod' (dividend divisor : ℕ) : Set where
  result : (q : ℕ) (r : Fin divisor)
           (eq : dividend ≡ toℕ r + q * divisor) →
           DivMod' dividend divisor

-- Integer division with remainder.

-- Note that Induction.Nat.<-rec is used to ensure termination of
-- division. The run-time complexity of this implementation of integer
-- division should be linear in the size of the dividend, assuming
-- that well-founded recursion and the equality type are optimised
-- properly (see "Inductive Families Need Not Store Their Indices"
-- (Brady, McBride, McKinna, TYPES 2003)).

_divMod'_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
            DivMod' dividend divisor
_divMod'_ m n {≢0} = <-rec Pred dm m n {≢0}
  where
  Pred : ℕ → Set
  Pred dividend = (divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
                  DivMod' dividend divisor

  1+_ : ∀ {k n} → DivMod' (suc k) n → DivMod' (suc n + k) n
  1+_ {k} {n} (result q r eq) = result (1 + q) r (lem₃ n k q r eq)

  dm : (dividend : ℕ) → <-Rec Pred dividend → Pred dividend
  dm m       rec zero    {≢0 = ()}
  dm zero    rec (suc n)            = result 0 zero refl
  dm (suc m) rec (suc n)            with compare m n
  dm (suc m) rec (suc .(suc m + k)) | less .m k    = result 0 r  (lem₁ m k)
                                        where r = suc (Fin.inject+ k (fromℕ m))
  dm (suc m) rec (suc .m)           | equal .m     = result 1 zero (lem₂ m)
  dm (suc .(suc n + k)) rec (suc n) | greater .n k =
    1+ rec (suc k) le (suc n)
    where le = s≤′s (s≤′s (n≤′m+n n k))

-- A variant.

_divMod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
           DivMod dividend divisor
_divMod_ m n {≢0} with _divMod'_ m n {≢0}
.(toℕ r + q * n) divMod n | result q r refl = result q r

-- Integer division.

_div_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
_div_ m n {≢0} with _divMod_ m n {≢0}
.(toℕ r + q * n) div n | result q r = q

-- The remainder after integer division.

_mod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → Fin divisor
_mod_ m n {≢0} with _divMod_ m n {≢0}
.(toℕ r + q * n) mod n | result q r = r
