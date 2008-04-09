------------------------------------------------------------------------
-- Integer division
------------------------------------------------------------------------

-- The run-time complexity of this implementation of integer division
-- should be linear in the size of the dividend, assuming that
-- well-founded recursion and the equality type are optimised properly
-- (see "Inductive Families Need Not Store Their Indices" (Brady,
-- McBride, McKinna, TYPES 2003)).

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

------------------------------------------------------------------------
-- Some boring lemmas

private

  lem₁ = \m k -> begin
    m
      ≡⟨ inject-lemma m k ⟩
    toℕ (inject k (fromℕ m))
      ≡⟨ (let X = var fz in
         prove (toℕ (inject k (fromℕ m)) ∷ []) X (X :+ con 0) ≡-refl) ⟩
    toℕ (inject k (fromℕ m)) + 0
      ∎

  lem₂ = \n ->
    let N = var fz in
    prove (n ∷ []) (con 1 :+ N) (con 1 :+ (N :+ con 0)) ≡-refl

  lem₃ = \n k x r eq -> begin
      suc (suc (n + k))
        ≡⟨ (let N = var fz; K = var (fs fz) in
            prove (suc n ∷ k ∷ [])
                  (con 1 :+ (N :+ K)) (N :+ (con 1 :+ K))
                  ≡-refl) ⟩
      suc n + suc k
        ≡⟨ ≡-cong (_+_ (suc n)) eq ⟩
      suc n + (toℕ r + x * suc n)
        ≡⟨ (let N = var fz; R = var (fs fz); X = var (fs (fs fz)) in
            prove (suc n ∷ toℕ r ∷ x ∷ [])
                  (N :+ (R :+ X :* N)) (R :+ (con 1 :+ X) :* N)
                  ≡-refl) ⟩
      toℕ r + suc x * suc n
        ∎

------------------------------------------------------------------------
-- Division

-- The specification of integer division.

data Result (dividend divisor : ℕ) : Set where
  result : (n : ℕ) (r : Fin divisor) ->
           dividend ≡ toℕ r + n * divisor ->
           Result dividend divisor

-- The implementation. Note that Logic.Induction.Nat is used to ensure
-- termination of division.

private

  Pred : ℕ -> Set
  Pred dividend = (divisor : ℕ) {≢0 : False (divisor ℕ-≟ 0)} ->
                  Result dividend divisor

  helper : forall m n {o} ->
           Ordering m o -> o ≡ suc n -> <-Rec Pred m ->
           Result m (suc n)
  -- m < suc n.
  helper .m .(m + k) (less m k) ≡-refl rec =
    result 0 (inject k (fromℕ m)) (lem₁ m k)

  -- m ≡ suc n.
  helper .(suc n) .n (equal (suc n)) ≡-refl rec =
    result 1 fz (lem₂ n)

  -- m > suc n.
  helper .(suc (suc (n + k))) .n (greater (suc n) k) ≡-refl rec
    with rec (suc k) (s≤′s (s≤′s (n≤′m+n n k))) (suc n)
  ... | result x r eq = result (suc x) r (lem₃ n k x r eq)

  -- Impossible cases.
  helper ._ _ (equal zero)     () _
  helper ._ _ (greater zero _) () _

  divMod' : (dividend : ℕ) -> <-Rec Pred dividend -> Pred dividend
  divMod' m rec zero    {≢0 = ()}
  divMod' m rec (suc n) = helper m n (compare m (suc n)) ≡-refl rec

-- And the interface.

_divMod_ : (dividend divisor : ℕ) {≢0 : False (divisor ℕ-≟ 0)} ->
           Result dividend divisor
_divMod_ = <-rec Pred divMod'

_div_ : (dividend divisor : ℕ) {≢0 : False (divisor ℕ-≟ 0)} -> ℕ
_div_ m n {≢0} with _divMod_ m n {≢0}
... | result x _ _ = x

_mod_ : (dividend divisor : ℕ) {≢0 : False (divisor ℕ-≟ 0)} ->
        Fin divisor
_mod_ m n {≢0} with _divMod_ m n {≢0}
... | result _ r _ = r
