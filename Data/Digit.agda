------------------------------------------------------------------------
-- Digits and digit expansions
------------------------------------------------------------------------

module Data.Digit where

open import Data.Nat
open import Data.Nat.Properties
open SemiringSolver
open import Data.Fin using (Fin; zero; suc; #_; toℕ)
open import Relation.Nullary
open import Data.Char using (Char)
open import Data.List
import Data.Vec as Vec
open import Induction.Nat
open import Data.Nat.DivMod
open ≤-Reasoning
open import Relation.Binary.PropositionalEquality
open import Data.Function

------------------------------------------------------------------------
-- A boring lemma

private

  lem : forall x k r -> 2 + x ≤′ r + (1 + x) * (2 + k)
  lem x k r = ≤⇒≤′ $ begin
    2 + x
      ≤⟨ m≤m+n _ _ ⟩
    2 + x + (x + (1 + x) * k + r)
      ≡⟨ (let X = var (# 0); R = var (# 1); K = var (# 2) in
         prove (Vec.fromList (x ∷ r ∷ k ∷ []))
               (con 2 :+ X :+ (X :+ (con 1 :+ X) :* K :+ R))
               (R :+ (con 1 :+ X) :* (con 2 :+ K))
               ≡-refl) ⟩
    r + (1 + x) * (2 + k)
      ∎

------------------------------------------------------------------------
-- Digits

-- Digit b is the type of digits in base b.

Digit : ℕ -> Set
Digit b = Fin b

-- Some specific digit kinds.

Decimal = Digit 10
Bit     = Digit 2

-- Some named digits.

0b : Bit
0b = zero

1b : Bit
1b = suc zero

------------------------------------------------------------------------
-- Showing digits

-- showDigit shows digits in base ≤ 16.
--
-- This function could be simplified by making use of some properties
-- of Unicode code points and adding another primitive character
-- function.

showDigit : forall {base} {base≤16 : True (base ≤? 16)} ->
            Digit base -> Char
showDigit zero = '0'
showDigit (suc zero) = '1'
showDigit (suc (suc zero)) = '2'
showDigit (suc (suc (suc zero))) = '3'
showDigit (suc (suc (suc (suc zero)))) = '4'
showDigit (suc (suc (suc (suc (suc zero))))) = '5'
showDigit (suc (suc (suc (suc (suc (suc zero)))))) = '6'
showDigit (suc (suc (suc (suc (suc (suc (suc zero))))))) = '7'
showDigit (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = '8'
showDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = '9'
showDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = 'a'
showDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = 'b'
showDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) = 'c'
showDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) = 'd'
showDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) = 'e'
showDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))) = 'f'
showDigit {base≤16 = base≤16}
          (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc i))))))))))))))))
          with witnessToTruth base≤16
showDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ()))))))))))))))))
  | (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))

------------------------------------------------------------------------
-- Digit expansions

-- fromDigits takes a digit expansion of a natural number, starting
-- with the _least_ significant digit, and returns the corresponding
-- natural number.

fromDigits : forall {base} -> List (Fin base) -> ℕ
fromDigits        []       = 0
fromDigits {base} (d ∷ ds) = toℕ d + fromDigits ds * base

-- toDigits b n yields the digits of n, in base b, starting with the
-- _least_ significant digit.
--
-- Note that the list of digits is always non-empty.
--
-- This function should be linear in n, if optimised properly (see
-- Data.Nat.DivMod).

data Digits (base : ℕ) : ℕ -> Set where
  digits : (ds : List (Fin base)) -> Digits base (fromDigits ds)

toDigits : (base : ℕ) {base≥2 : True (2 ≤? base)} (n : ℕ) ->
           Digits base n
toDigits zero       {base≥2 = ()} _
toDigits (suc zero) {base≥2 = ()} _
toDigits (suc (suc k)) n = <-rec Pred helper n
  where
  base = suc (suc k)
  Pred = Digits base

  cons : forall {n} (r : Fin base) -> Pred n -> Pred (toℕ r + n * base)
  cons r (digits ds) = digits (r ∷ ds)

  helper : forall n -> <-Rec Pred n -> Pred n
  helper n rec with n divMod base
  helper .(toℕ r + 0     * base) rec | result zero    r = digits (r ∷ [])
  helper .(toℕ r + suc x * base) rec | result (suc x) r =
    cons r (rec (suc x) (lem (pred (suc x)) k (toℕ r)))

theDigits : (base : ℕ) {base≥2 : True (2 ≤? base)} (n : ℕ) ->
            List (Fin base)
theDigits base {base≥2} n       with toDigits base {base≥2} n
theDigits base .(fromDigits ds) | digits ds = ds
