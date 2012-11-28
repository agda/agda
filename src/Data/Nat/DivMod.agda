------------------------------------------------------------------------
-- The Agda standard library
--
-- Integer division
------------------------------------------------------------------------

module Data.Nat.DivMod where

open import Data.Nat as Nat
open import Data.Nat.Properties
open SemiringSolver
open import Data.Fin as Fin using (Fin; zero; suc; toℕ; fromℕ)
import Data.Fin.Props as Fin
open import Induction.Nat
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function

------------------------------------------------------------------------
-- Some boring lemmas

private

  lem₁ : (m k : ℕ) →
         Nat.suc m ≡ suc (toℕ (Fin.inject+ k (fromℕ m)) + 0)
  lem₁ m k = cong suc $ begin
    m
      ≡⟨ sym $ Fin.to-from m ⟩
    toℕ (fromℕ m)
      ≡⟨ Fin.inject+-lemma k (fromℕ m) ⟩
    toℕ (Fin.inject+ k (fromℕ m))
      ≡⟨ solve 1 (λ x → x := x :+ con 0) refl _ ⟩
    toℕ (Fin.inject+ k (fromℕ m)) + 0
      ∎

  lem₂ : ∀ n → _
  lem₂ = solve 1 (λ n → con 1 :+ n  :=  con 1 :+ (n :+ con 0)) refl

  lem₃ : ∀ n k q (r : Fin n) eq → suc n + k ≡ toℕ r + suc q * n
  lem₃ n k q r eq = begin
      suc n + k
        ≡⟨ solve 2 (λ n k → con 1 :+ n :+ k  :=  n :+ (con 1 :+ k))
                   refl n k ⟩
      n + suc k
        ≡⟨ cong (_+_ n) eq ⟩
      n + (toℕ r + q * n)
        ≡⟨ solve 3 (λ n r q → n :+ (r :+ q :* n)  :=
                              r :+ (con 1 :+ q) :* n)
                   refl n (toℕ r) q ⟩
      toℕ r + suc q * n
        ∎

------------------------------------------------------------------------
-- Division

-- A specification of integer division.

record DivMod (dividend divisor : ℕ) : Set where
  constructor result
  field
    quotient  : ℕ
    remainder : Fin divisor
    property  : dividend ≡ toℕ remainder + quotient * divisor

-- Integer division with remainder.

-- Note that Induction.Nat.<-rec is used to establish termination of
-- division. The run-time complexity of this implementation of integer
-- division should be linear in the size of the dividend, assuming
-- that well-founded recursion and the equality type are optimised
-- properly (see "Inductive Families Need Not Store Their Indices"
-- (Brady, McBride, McKinna, TYPES 2003)).

_divMod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
           DivMod dividend divisor
_divMod_ m n {≢0} = <-rec Pred dm m n {≢0}
  where
  Pred : ℕ → Set
  Pred dividend = (divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
                  DivMod dividend divisor

  1+_ : ∀ {k n} → DivMod (suc k) n → DivMod (suc n + k) n
  1+_ {k} {n} (result q r eq) = result (1 + q) r (lem₃ n k q r eq)

  dm : (dividend : ℕ) → <-Rec Pred dividend → Pred dividend
  dm m       rec zero    {≢0 = ()}
  dm zero    rec (suc n)            = result 0 zero refl
  dm (suc m) rec (suc n)            with compare m n
  dm (suc m) rec (suc .(suc m + k)) | less .m k    = result 0 r (lem₁ m k)
                                        where r = suc (Fin.inject+ k (fromℕ m))
  dm (suc m) rec (suc .m)           | equal .m     = result 1 zero (lem₂ m)
  dm (suc .(suc n + k)) rec (suc n) | greater .n k =
    1+ rec (suc k) le (suc n)
    where le = s≤′s (s≤′s (n≤′m+n n k))

-- Integer division.

_div_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
_div_ m n {≢0} = DivMod.quotient $ _divMod_ m n {≢0}

-- The remainder after integer division.

_mod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → Fin divisor
_mod_ m n {≢0} = DivMod.remainder $ _divMod_ m n {≢0}
