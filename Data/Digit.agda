------------------------------------------------------------------------
-- Digits and digit expansions
------------------------------------------------------------------------

module Data.Digit where

open import Data.Nat
open import Data.Nat.Properties
open ℕ-semiringSolver
open import Data.Fin
open import Relation.Nullary
open import Data.Char using (Char)
open import Data.List
import Data.Vec as Vec
open import Logic.Induction.Nat
open import Data.Nat.DivMod
open import Algebra.Structures
open import Data.Nat.Properties
open ≤-Reasoning
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Logic

------------------------------------------------------------------------
-- Some boring lemmas

private

  lem₀ : forall r k -> r + (k * 0 + 0 + 0) ≡ r
  lem₀ r k = prove (Vec.fromList (r ∷ k ∷ []))
                   (R :+ (K :* con 0 :+ con 0 :+ con 0)) R
                   ≡-refl
    where R = var fz; K = var (fs fz)

  lem₁ : forall x k r -> 1 ≤ x -> 1 + x ≤ x * (2 + k) + r
  lem₁ x k r 1≤x = begin
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
    x * (2 + k) + r
      ∎
    where open IsCommutativeSemiring _ ℕ-isCommutativeSemiring

  lem₂ : forall {s} x r k -> s ≡ x -> r + k * s ≡ x * k + r
  lem₂ x r k ≡-refl =
    prove (Vec.fromList (x ∷ r ∷ k ∷ []))
          (R :+ K :* X) (X :* K :+ R)
          ≡-refl
    where X = var fz; R = var (fs fz); K = var (fs (fs fz))

------------------------------------------------------------------------
-- Digits

-- Digit b is the type of digits in base b.

Digit : ℕ -> Set
Digit b = Fin b

------------------------------------------------------------------------
-- Showing digits

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
-- Digit expansions

-- fromDigits takes a digit expansion of a natural number, starting
-- with the _least_ significant digit, and returns the corresponding
-- natural number.

fromDigits : forall {base} -> [ Fin base ] -> ℕ
fromDigits        []       = 0
fromDigits {base} (d ∷ ds) = toℕ d + base * fromDigits ds

-- digits b n yields the digits of n, in base b, starting with the
-- _least_ significant digit.
--
-- Note that the list of digits is always non-empty.

digits : (base : ℕ) {base≥2 : True (2 ≤? base)} (n : ℕ) ->
         ∃ [ Fin base ] (\ds -> fromDigits ds ≡ n)
digits zero       {base≥2 = ()} _
digits (suc zero) {base≥2 = ()} _
digits base@(suc (suc k)) n = <-rec Pred helper n
  where
  Pred = \n -> ∃ [ Fin base ] (\ds -> fromDigits ds ≡ n)

  helper : forall n -> <-Rec Pred n -> Pred n
  helper n rec with n divMod base

  helper .(toℕ r) rec | result zero r ≡-refl =
    exists (r ∷ []) (lem₀ (toℕ r) k)

  helper .(x * base + toℕ r) rec | result x@(suc _) r ≡-refl
    with rec x (lem₁ x k (toℕ r) (s≤s z≤n))
  helper .(x * base + toℕ r) rec | result (suc m) r ≡-refl
                                 | exists rs eq =
    exists (r ∷ rs) (lem₂ (suc m) (toℕ r) base eq)

toDigits : (base : ℕ) {base≥2 : True (2 ≤? base)} -> ℕ -> [ Fin base ]
toDigits base {base≥2} n = witness (digits base {base≥2} n)
