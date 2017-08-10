------------------------------------------------------------------------
-- The Agda standard library
--
-- Digits and digit expansions
------------------------------------------------------------------------

module Data.Digit where

open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_; _≤?_; _≤′_)
open import Data.Nat.Properties
open SemiringSolver
open import Data.Fin as Fin using (Fin; zero; suc; toℕ)
open import Data.Char using (Char)
open import Data.List.Base
open import Data.Product
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.Nat.DivMod
open import Induction.Nat using (<′-rec; <′-Rec)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Function

------------------------------------------------------------------------
-- Digits

-- Digit b is the type of digits in base b.

Digit : ℕ → Set
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

-- The characters used to show the first 16 digits.

digitChars : Vec Char 16
digitChars =
  '0' ∷ '1' ∷ '2' ∷ '3' ∷ '4' ∷ '5' ∷ '6' ∷ '7' ∷ '8' ∷ '9' ∷
  'a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ 'e' ∷ 'f' ∷ []

-- showDigit shows digits in base ≤ 16.

showDigit : ∀ {base} {base≤16 : True (base ≤? 16)} →
            Digit base → Char
showDigit {base≤16 = base≤16} d =
  Vec.lookup (Fin.inject≤ d (toWitness base≤16)) digitChars

------------------------------------------------------------------------
-- Digit expansions

Expansion : ℕ → Set
Expansion base = List (Fin base)

-- fromDigits takes a digit expansion of a natural number, starting
-- with the _least_ significant digit, and returns the corresponding
-- natural number.

fromDigits : ∀ {base} → Expansion base → ℕ
fromDigits        []       = 0
fromDigits {base} (d ∷ ds) = toℕ d + fromDigits ds * base

-- toDigits b n yields the digits of n, in base b, starting with the
-- _least_ significant digit.
--
-- Note that the list of digits is always non-empty.

toDigits : (base : ℕ) {base≥2 : True (2 ≤? base)} (n : ℕ) →
           ∃ λ (ds : Expansion base) → fromDigits ds ≡ n
toDigits zero       {base≥2 = ()} _
toDigits (suc zero) {base≥2 = ()} _
toDigits (suc (suc k)) n = <′-rec Pred helper n
  where
  base = suc (suc k)
  Pred = λ n → ∃ λ ds → fromDigits ds ≡ n

  cons : ∀ {m} (r : Fin base) → Pred m → Pred (toℕ r + m * base)
  cons r (ds , eq) = (r ∷ ds , P.cong (λ i → toℕ r + i * base) eq)

  open ≤-Reasoning

  lem : ∀ x k r → 2 + x ≤′ r + (1 + x) * (2 + k)
  lem x k r = ≤⇒≤′ $ begin
    2 + x
      ≤⟨ m≤m+n _ _ ⟩
    2 + x + (x + (1 + x) * k + r)
      ≡⟨ solve 3 (λ x r k → con 2 :+ x :+ (x :+ (con 1 :+ x) :* k :+ r)
                              :=
                            r :+ (con 1 :+ x) :* (con 2 :+ k))
                 refl x r k ⟩
    r + (1 + x) * (2 + k)
      ∎

  helper : ∀ n → <′-Rec Pred n → Pred n
  helper n                       rec with n divMod base
  helper .(toℕ r + 0     * base) rec | result zero    r refl = ([ r ] , refl)
  helper .(toℕ r + suc x * base) rec | result (suc x) r refl =
    cons r (rec (suc x) (lem (pred (suc x)) k (toℕ r)))

