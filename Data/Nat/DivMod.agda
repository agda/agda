------------------------------------------------------------------------
-- Integer division
------------------------------------------------------------------------

-- Note that this implementation is very slow; but if you need fast
-- integer division, do not use unary numbers.

-- For some reason Agda panics when checking the pattern completeness
-- of helper.

{-# OPTIONS --no-coverage-check
  #-}

module Data.Nat.DivMod where

open import Data.Nat
open import Data.Nat.Properties
open ℕ-semiringSolver
open import Logic
open import Data.Fin
open import Data.Fin.Props
open import Logic.Induction.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Vec

-- The specification of integer division.

data Result (divisor dividend : ℕ) : Set where
  result : (n : ℕ) (r : Fin dividend) ->
           divisor ≡ n * dividend + toℕ r ->
           Result divisor dividend

-- The implementation. Note that Logic.Induction.Nat is used to ensure
-- termination of division.

private

  Pred : ℕ -> Set
  Pred divisor = (dividend : ℕ) {≢0 : False (dividend ℕ-≟ 0)} ->
                 Result divisor dividend

  helper : forall m n {o} ->
           Ordering m o -> o ≡ suc n -> <-Rec Pred m ->
           Result m (suc n)
  -- m < suc n.
  helper .m .(m + k) (less m k) ≡-refl rec =
    result 0 (inject k (fromℕ m)) (inject-lemma m k)

  -- m ≡ suc n.
  helper .(suc n) .n (equal (suc n)) ≡-refl rec =
    result 1 fz lemma
    where
    N     = var fz
    lemma = prove (n ∷ []) (con 1 :+ N) (con 1 :+ (N :+ con 0)) ≡-refl

  -- m > suc n.
  helper .(suc (suc (n + k))) .n (greater (suc n) k) ≡-refl rec
    with rec (suc k) (s≤s (s≤s (n≤m+n n k))) (suc n)
  ... | result x r eq = result (suc x) r lemma
    where
    lemma = begin
      suc (suc (n + k))
        ≡⟨ (let N = var fz; K = var (fs fz) in
            prove (suc n ∷ k ∷ [])
                  (con 1 :+ (N :+ K)) (N :+ (con 1 :+ K))
                  ≡-refl) ⟩
      suc n + suc k
        ≡⟨ ≡-cong (_+_ (suc n)) eq ⟩
      suc n + (x * suc n + toℕ r)
        ≡⟨ (let A = var fz; B = var (fs fz); C = var (fs (fs fz)) in
            prove (suc n ∷ x * suc n ∷ toℕ r ∷ [])
                  (A :+ (B :+ C)) ((B :+ A) :+ C)
                  ≡-refl) ⟩
      (x * suc n + suc n) + toℕ r
        ∎

  -- Impossible cases.
  helper ._ _ (equal zero)     () _
  helper ._ _ (greater zero _) () _

  divMod' : (divisor : ℕ) -> <-Rec Pred divisor -> Pred divisor
  divMod' m rec zero    {≢0 = ()}
  divMod' m rec (suc n) = helper m n (compare m (suc n)) ≡-refl rec

-- And the interface.

_divMod_ : (divisor dividend : ℕ) {≢0 : False (dividend ℕ-≟ 0)} ->
           Result divisor dividend
_divMod_ = <-rec Pred divMod'
