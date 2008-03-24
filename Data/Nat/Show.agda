------------------------------------------------------------------------
-- Showing natural numbers
------------------------------------------------------------------------

module Data.Nat.Show where

open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
open ≤-Reasoning
open import Algebra.Structures
open import Data.Product
open import Data.List
open import Data.Function
open import Data.Fin
open import Logic.Induction.Nat
import Data.String as String
open String using (String)
import Data.Char as Char
open Char using (Char)
open import Logic
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

------------------------------------------------------------------------
-- Digits

-- Digit b is the type of digits in base b.

Digit : ℕ -> Set
Digit b = Fin b

-- showDigit shows digits in base ≤ 16.
--
-- This function could be simplified by making use of some properties
-- of Unicode code points and adding another primitive character
-- function.

showDigit : forall {base} {base≤16 : True (base ≤? 16)} ->
            Digit base -> Char
showDigit fz = '0'
showDigit (fs fz) = '1'
showDigit (fs (fs fz)) = '2'
showDigit (fs (fs (fs fz))) = '3'
showDigit (fs (fs (fs (fs fz)))) = '4'
showDigit (fs (fs (fs (fs (fs fz))))) = '5'
showDigit (fs (fs (fs (fs (fs (fs fz)))))) = '6'
showDigit (fs (fs (fs (fs (fs (fs (fs fz))))))) = '7'
showDigit (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))) = '8'
showDigit (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))) = '9'
showDigit (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))) = 'a'
showDigit (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))))) = 'b'
showDigit (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))))) = 'c'
showDigit (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))))))) = 'd'
showDigit (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))))))) = 'e'
showDigit (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))))))))) = 'f'
showDigit {base≤16 = base≤16}
          (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs i))))))))))))))))
          with witnessToTruth base≤16
showDigit (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs ()))))))))))))))))
  | (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))

------------------------------------------------------------------------
-- Showing natural numbers

-- digits b ge n yields the digits of n, in base b, starting with the
-- _least_ significant digit.
--
-- Note: As a special case the expansion of n in base 1 consists of
-- n + 1 zeros.

digits : (base : ℕ) {base≥1 : True (1 ≤? base)} -> ℕ -> [ Fin base ]
digits zero {base≥1 = ()} _
digits (suc zero)         n = replicate (suc n) fz
digits base@(suc (suc k)) n = <-rec Pred helper n
  where
  Pred = \_ -> [ Fin base ]

  helper : forall n -> <-Rec Pred n -> Pred n
  helper n rec with n divMod base
  helper .(toℕ r)            rec | result zero      r ≡-refl = r ∷ []
  helper .(x * base + toℕ r) rec | result x@(suc _) r ≡-refl =
    r ∷ rec x lemma
    where
    open IsCommutativeSemiring _ ℕ-isCommutativeSemiring

    1≤x : 1 ≤ x
    1≤x = s≤s z≤n

    lemma = begin
      1 + x
        ≤⟨ 1≤x +-mono byDef ⟩
      x + x
        ≡⟨ *-comm 2 x ⟩
      x * 2
        ≤⟨ n≤n+m _ _ ⟩
      x * 2 + x * k
        ≡⟨ ≡-sym (proj₁ distrib x 2 k) ⟩
      x * (2 + k)
        ≤⟨ n≤n+m _ _ ⟩
      x * base + toℕ r
        ∎

-- showInBase b n is a string containing the representation of n in
-- base b.

showInBase : (base : ℕ)
             {base≥1 : True (1 ≤? base)}
             {base≤16 : True (base ≤? 16)} ->
             ℕ -> String
showInBase base {base≥1} {base≤16} =
  String.fromList ∘
  map (showDigit {base≤16 = base≤16}) ∘
  reverse ∘
  digits base {base≥1 = base≥1}

-- show n is a string containing the decimal expansion of n (starting
-- with the most significant digit).

show : ℕ -> String
show = showInBase 10
